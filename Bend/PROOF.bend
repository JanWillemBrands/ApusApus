import Base
import ./TYPES.bend as Types
import ./GRAMMAR.bend as Grammar
import ./LAWS.bend as GrammarLaws
import ./LEMMAS.bend as Lemma

# Proofs of the laws in LAWS.bend.
#
# Soundness: every cell of the CYK table holds only nonterminals that have a parse
# tree for the slice of the input the cell describes (CellsSound, table_sound).
#
# Completeness: by induction over a parse tree, its nonterminal is in the cell for
# the slice the tree spells (cell_complete).
#
# Binary subtree sets, soundness: every element of the set is a correct step
# (set_ok), so a fitting tree embedded in the set spells the input (tree_spells).
#
# Binary subtree sets, completeness: by induction over a parse tree, the step of
# each of its nodes is in the set (tree_in_set), using cell_complete for the
# nonterminals of the two halves.


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
  {GrammarLaws.lhsIs(grammar, o, lhs) == True{} : Bool}

def lhs_at(grammar, o, lhs, rhs, r, e):
  match grammar o:
    case Nil{} 0n:
      Empty.absurd({GrammarLaws.lhsIs([], 0n, lhs) == True{} : Bool}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Nil{} 1n+q:
      Empty.absurd({GrammarLaws.lhsIs([], 1n+q, lhs) == True{} : Bool}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Con{h, t} 0n:
      %Equal.sym(+List<Types.Production>, h <> t, Types.Production{lhs, rhs} <> r, e) : {GrammarLaws.lhsIs(_, 0n, lhs) == True{} : Bool}
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
  {GrammarLaws.rhsOf(grammar, o) == rhs : +List<Types.Symbol>}

def rhs_at(grammar, o, lhs, rhs, r, e):
  match grammar o:
    case Nil{} 0n:
      Empty.absurd({GrammarLaws.rhsOf([], 0n) == rhs : +List<Types.Symbol>}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Nil{} 1n+q:
      Empty.absurd({GrammarLaws.rhsOf([], 1n+q) == rhs : +List<Types.Symbol>}, productions_nil_is_not_cons(Types.Production{lhs, rhs}, r, e))
    case Con{h, t} 0n:
      %Equal.sym(+List<Types.Production>, h <> t, Types.Production{lhs, rhs} <> r, e) : {GrammarLaws.rhsOf(_, 0n) == rhs : +List<Types.Symbol>}
      {==}
    case Con{Types.Production{hl, hr}, t} 1n+q:
      rhs_at(t, q, lhs, rhs, r, e)



# Children that fit rhs fit the rhs of the production at index o.
law fits_rhs:
  for +grammar: +List<Types.Production>
  for +o: Nat
  for -lhs: Nat
  for +rhs: +List<Types.Symbol>
  for -r: +List<Types.Production>
  for tail: {dropP(o, grammar) == Types.Production{lhs, rhs} <> r : +List<Types.Production>}
  for -children: +List<Types.Tree>
  for e: {GrammarLaws.fits(children, grammar, rhs) == True{} : Bool}
  {GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, o)) == True{} : Bool}

def fits_rhs(grammar, o, lhs, rhs, r, tail, children, e):
  %Equal.sym(+List<Types.Symbol>, GrammarLaws.rhsOf(grammar, o), rhs, rhs_at(grammar, o, lhs, rhs, r, tail)) : {GrammarLaws.fits(children, grammar, _) == True{} : Bool}
  e



# A node for the production at index o fits its lhs, when its children fit its rhs.
law node_fits:
  for +grammar: +List<Types.Production>
  for +o: Nat
  for +lhs: Nat
  for +rhs: +List<Types.Symbol>
  for +r: +List<Types.Production>
  for +tail: {dropP(o, grammar) == Types.Production{lhs, rhs} <> r : +List<Types.Production>}
  for +children: +List<Types.Tree>
  for e: {GrammarLaws.fits(children, grammar, rhs) == True{} : Bool}
  {GrammarLaws.fits([Types.Node{o, children}], grammar, [Types.Nonterminal{lhs}]) == True{} : Bool}

def node_fits(grammar, o, lhs, rhs, r, tail, children, e):
  Lemma.and_true_intro(
    GrammarLaws.lhsIs(grammar, o, lhs),
    Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, o)), True{}),
    lhs_at(grammar, o, lhs, rhs, r, tail),
    Lemma.and_true_intro(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, o)), True{}, fits_rhs(grammar, o, lhs, rhs, r, tail, children, e), {==}))



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
      inner = Lemma.and_true_right_side(GrammarLaws.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), True{}), first)
      Lemma.and_true_intro(
        GrammarLaws.lhsIs(grammar, index, id),
        Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)),
        Lemma.and_true_left(GrammarLaws.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), True{}), first),
        Lemma.and_true_intro(
          GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)),
          GrammarLaws.fits(ts, grammar, ss),
          Lemma.and_true_left(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), True{}, inner),
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



# ======== CYK: SOUNDNESS ========

# ---- What a nonterminal derives ----
#
# Copyable (Data) versions of "a tree for nonterminal a spells w", so that the
# proofs can use one such fact many times.

def NtDerives(+grammar: +List<Types.Production>, +a: Nat, +w: +List<Nat>) -> Data:
  Sigma<&2, &2, Types.Tree, t => Sigma<&2, &2, {GrammarLaws.fits([t], grammar, [Types.Nonterminal{a}]) == True{} : Bool}, fitting => {GrammarLaws.leaves([t]) == w : +List<Nat>}>>



# Every nonterminal in the list derives w.
def AllDerive(+grammar: +List<Types.Production>, nts: +List<Nat>, +w: +List<Nat>) -> Data:
  match nts:
    case Nil{}:
      Unit
    case Con{a, rest}:
      Sigma<&2, &2, NtDerives(grammar, a, w), here => AllDerive(grammar, rest, w)>



law kind_matches:
  for +k: Nat
  for -kind: Nat
  for e: {k == kind : Nat}
  {Nat.is_eq(kind, k) == True{} : Bool}

def kind_matches(k, kind, e):
  %e : {Nat.is_eq(_, k) == True{} : Bool}
  Lemma.nat_eq_refl(k)



# The tree for A = "k" at index o, with k == kind, spells [kind].
law terminal_tree:
  for +grammar: +List<Types.Production>
  for +o: Nat
  for +lhs: Nat
  for +k: Nat
  for +kind: Nat
  for +r: +List<Types.Production>
  for +tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Terminal{k}]} <> r : +List<Types.Production>}
  for e: {k == kind : Nat}
  NtDerives(grammar, lhs, [kind])

def terminal_tree(grammar, o, lhs, k, kind, r, tail, e):
  (Types.Node{o, [Types.Leaf{kind}]}, (node_fits(grammar, o, lhs, [Types.Terminal{k}], r, tail, [Types.Leaf{kind}], Lemma.and_true_intro(Nat.is_eq(kind, k), True{}, kind_matches(k, kind, e), {==})), {==}))



# The tree for A = B C at index o, from trees for B and C.
law binary_tree:
  for +grammar: +List<Types.Production>
  for +o: Nat
  for +lhs: Nat
  for +b: Nat
  for +c: Nat
  for +r: +List<Types.Production>
  for +tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]} <> r : +List<Types.Production>}
  for +wl: +List<Nat>
  for +wr: +List<Nat>
  for left: NtDerives(grammar, b, wl)
  for right: NtDerives(grammar, c, wr)
  NtDerives(grammar, lhs, List.append(&2, Nat, wl, wr))

def binary_tree(grammar, o, lhs, b, c, r, tail, wl, wr, left, right):
  match left:
    case (+tb, (fb, lb)):
      match right:
        case (+tc, (fc, lc)):
          children = fits_cons_intro(tb, [tc], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fb, fits_cons_intro(tc, [], Types.Nonterminal{c}, [], grammar, fc, {==}))
          (Types.Node{o, [tb, tc]}, (node_fits(grammar, o, lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}], r, tail, [tb, tc], children), node_leaves(o, [tb, tc], List.append(&2, Nat, wl, wr), pair_leaves(tb, tc, wl, wr, lb, lc))))



law member_pick:
  for -grammar: +List<Types.Production>
  for -w: +List<Nat>
  for +x: Nat
  for +y: Nat
  for -rest: +List<Nat>
  for cases: Either<{Nat.is_eq(x, y) == True{} : Bool}, {Grammar.natMember(x, rest) == True{} : Bool}>
  for here: NtDerives(grammar, y, w)
  for searchRest: {Grammar.natMember(x, rest) == True{} : Bool} -> NtDerives(grammar, x, w)
  NtDerives(grammar, x, w)

def member_pick(grammar, w, x, y, rest, cases, here, searchRest):
  match cases:
    case Inl{isY}:
      %Equal.sym(Nat, x, y, Lemma.nat_eq_sound(x, y, isY)) : NtDerives(grammar, _, w)
      here
    case Inr{inRest}:
      searchRest(inRest)



# A nonterminal found in a sound list derives w.
law member_sound:
  for +grammar: +List<Types.Production>
  for +w: +List<Nat>
  for +x: Nat
  for nts: +List<Nat>
  for e: {Grammar.natMember(x, nts) == True{} : Bool}
  for all: AllDerive(grammar, nts, w)
  NtDerives(grammar, x, w)

def member_sound(grammar, w, x, nts, e, all):
  match nts:
    case Nil{}:
      Empty.absurd(NtDerives(grammar, x, w), Lemma.false_is_not_true(e))
    case Con{+y, +rest}:
      match all:
        case (here, later):
          member_pick(
            grammar, w, x, y, rest,
            Lemma.or_true_cases(Nat.is_eq(x, y), Grammar.natMember(x, rest), e),
            here,
            inRest => member_sound(grammar, w, x, rest, inRest, later))



# ---- The grammar scans only return correct nonterminals ----

law keep_terminal:
  for +grammar: +List<Types.Production>
  for +kind: Nat
  for +lhs: Nat
  for +k: Nat
  for +rest: +List<Types.Production>
  for +o: Nat
  for keep: Bool
  for keptEq: {Nat.is_eq(k, kind) == keep : Bool}
  for tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Terminal{k}]} <> rest : +List<Types.Production>}
  for later: AllDerive(grammar, Grammar.terminalNonterminals(rest, kind), [kind])
  AllDerive(grammar, Grammar.keepNat(keep, lhs, Grammar.terminalNonterminals(rest, kind)), [kind])

def keep_terminal(grammar, kind, lhs, k, rest, o, keep, keptEq, tail, later):
  match keep:
    case False{}:
      later
    case True{}:
      (terminal_tree(grammar, o, lhs, k, kind, rest, tail, Lemma.nat_eq_sound(k, kind, keptEq)), later)



# Every nonterminal that terminalNonterminals returns derives [kind].
law terminal_nts_sound:
  for +grammar: +List<Types.Production>
  for +kind: Nat
  for rest: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == rest : +List<Types.Production>}
  AllDerive(grammar, Grammar.terminalNonterminals(rest, kind), [kind])

def terminal_nts_sound(grammar, kind, rest, o, tail):
  match rest:
    case Nil{}:
      Unit{}
    case Con{Types.Production{+lhs, [Types.Terminal{+k}]}, +others}:
      keep_terminal(
        grammar, kind, lhs, k, others, o,
        Nat.is_eq(k, kind), {==}, tail,
        terminal_nts_sound(grammar, kind, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Terminal{k}]}, others, tail)))
    case Con{Types.Production{+lhs, Nil{}}, +others}:
      terminal_nts_sound(grammar, kind, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, []}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Terminal{+k}, Con{+second, +more}}}, +others}:
      terminal_nts_sound(grammar, kind, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Terminal{k} <> second <> more}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+first}, +more}}, +others}:
      terminal_nts_sound(grammar, kind, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{first} <> more}, others, tail))



law keep_binary:
  for +grammar: +List<Types.Production>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +wl: +List<Nat>
  for +wr: +List<Nat>
  for +leftsSound: AllDerive(grammar, lefts, wl)
  for +rightsSound: AllDerive(grammar, rights, wr)
  for +lhs: Nat
  for +b: Nat
  for +c: Nat
  for +rest: +List<Types.Production>
  for +o: Nat
  for keep: Bool
  for +keptEq: {Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)) == keep : Bool}
  for +tail: {dropP(o, grammar) == Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]} <> rest : +List<Types.Production>}
  for later: AllDerive(grammar, Grammar.binaryNonterminals(rest, lefts, rights), List.append(&2, Nat, wl, wr))
  AllDerive(grammar, Grammar.keepNat(keep, lhs, Grammar.binaryNonterminals(rest, lefts, rights)), List.append(&2, Nat, wl, wr))

def keep_binary(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, lhs, b, c, rest, o, keep, keptEq, tail, later):
  match keep:
    case False{}:
      later
    case True{}:
      left = member_sound(grammar, wl, b, lefts, Lemma.and_true_left(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), keptEq), leftsSound)
      right = member_sound(grammar, wr, c, rights, Lemma.and_true_right_side(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), keptEq), rightsSound)
      (binary_tree(grammar, o, lhs, b, c, rest, tail, wl, wr, left, right), later)



# Every nonterminal that binaryNonterminals returns derives wl ++ wr.
law binary_nts_sound:
  for +grammar: +List<Types.Production>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +wl: +List<Nat>
  for +wr: +List<Nat>
  for +leftsSound: AllDerive(grammar, lefts, wl)
  for +rightsSound: AllDerive(grammar, rights, wr)
  for rest: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == rest : +List<Types.Production>}
  AllDerive(grammar, Grammar.binaryNonterminals(rest, lefts, rights), List.append(&2, Nat, wl, wr))

def binary_nts_sound(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, rest, o, tail):
  match rest:
    case Nil{}:
      Unit{}
    case Con{Types.Production{+lhs, [Types.Nonterminal{+b}, Types.Nonterminal{+c}]}, +others}:
      keep_binary(
        grammar, lefts, rights, wl, wr, leftsSound, rightsSound, lhs, b, c, others, o,
        Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), {==}, tail,
        binary_nts_sound(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Nonterminal{b}, Types.Nonterminal{c}]}, others, tail)))
    case Con{Types.Production{+lhs, Nil{}}, +others}:
      binary_nts_sound(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, []}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Terminal{+k}, +more}}, +others}:
      binary_nts_sound(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Terminal{k} <> more}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Nil{}}}, +others}:
      binary_nts_sound(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Nonterminal{b}]}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Con{Types.Terminal{+k}, +more}}}, +others}:
      binary_nts_sound(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{b} <> Types.Terminal{k} <> more}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+b}, Con{Types.Nonterminal{+c}, Con{+third, +more}}}}, +others}:
      binary_nts_sound(grammar, lefts, rights, wl, wr, leftsSound, rightsSound, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{b} <> Types.Nonterminal{c} <> third <> more}, others, tail))



# ---- The table only holds correct nonterminals ----

# Moving AllDerive along an equation between inputs.
law all_derive_at:
  for -grammar: +List<Types.Production>
  for -nts: +List<Nat>
  for -w1: +List<Nat>
  for -w2: +List<Nat>
  for e: {w1 == w2 : +List<Nat>}
  for all: AllDerive(grammar, nts, w1)
  AllDerive(grammar, nts, w2)

def all_derive_at(grammar, nts, w1, w2, e, all):
  %e : AllDerive(grammar, nts, _)
  all



law all_derive_append:
  for +grammar: +List<Types.Production>
  for +w: +List<Nat>
  for xs: +List<Nat>
  for -ys: +List<Nat>
  for first: AllDerive(grammar, xs, w)
  for second: AllDerive(grammar, ys, w)
  AllDerive(grammar, List.append(&2, Nat, xs, ys), w)

def all_derive_append(grammar, w, xs, ys, first, second):
  match xs:
    case Nil{}:
      second
    case Con{a, rest}:
      match first:
        case (here, later):
          (here, all_derive_append(grammar, w, rest, ys, later, second))



# CellsSound: every cell holds nonterminals that derive the slice it describes.
def CellsSound(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, table: +List<Grammar.Cell>) -> Data:
  match table:
    case Nil{}:
      Unit
    case Con{Grammar.Cell{start, length, nts}, rest}:
      Sigma<&2, &2, AllDerive(grammar, nts, Lemma.slice(inputTokens, start, length)), here => CellsSound(grammar, inputTokens, rest)>



law lookup_pick:
  for -grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +l: Nat
  for +cellStart: Nat
  for +cellLength: Nat
  for -nts: +List<Nat>
  for -later: +List<Nat>
  for found: Bool
  for +foundEq: {Bool.and(Nat.is_eq(cellLength, l), Nat.is_eq(cellStart, s)) == found : Bool}
  for here: AllDerive(grammar, nts, Lemma.slice(inputTokens, cellStart, cellLength))
  for laterSound: AllDerive(grammar, later, Lemma.slice(inputTokens, s, l))
  AllDerive(grammar, Grammar.pickCell(found, nts, later), Lemma.slice(inputTokens, s, l))

def lookup_pick(grammar, inputTokens, s, l, cellStart, cellLength, nts, later, found, foundEq, here, laterSound):
  match found:
    case False{}:
      laterSound
    case True{}:
      sameLength = Lemma.nat_eq_sound(cellLength, l, Lemma.and_true_left(Nat.is_eq(cellLength, l), Nat.is_eq(cellStart, s), foundEq))
      sameStart = Lemma.nat_eq_sound(cellStart, s, Lemma.and_true_right_side(Nat.is_eq(cellLength, l), Nat.is_eq(cellStart, s), foundEq))
      %sameStart : AllDerive(grammar, nts, Lemma.slice(inputTokens, _, l))
      %sameLength : AllDerive(grammar, nts, Lemma.slice(inputTokens, cellStart, _))
      here



# A lookup in a sound table returns nonterminals that derive the slice.
law lookup_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +l: Nat
  for table: +List<Grammar.Cell>
  for cells: CellsSound(grammar, inputTokens, table)
  AllDerive(grammar, Grammar.lookup(table, s, l), Lemma.slice(inputTokens, s, l))

def lookup_sound(grammar, inputTokens, s, l, table, cells):
  match table:
    case Nil{}:
      Unit{}
    case Con{Grammar.Cell{+cellStart, +cellLength, +nts}, +rest}:
      match cells:
        case (here, restSound):
          lookup_pick(
            grammar, inputTokens, s, l, cellStart, cellLength, nts, Grammar.lookup(rest, s, l),
            Bool.and(Nat.is_eq(cellLength, l), Nat.is_eq(cellStart, s)), {==},
            here,
            lookup_sound(grammar, inputTokens, s, l, rest, restSound))



# Every split combines two sound lookups, and the two slices join into the whole span.
law split_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +cells: CellsSound(grammar, inputTokens, table)
  for +s: Nat
  for left: Nat
  for +right: Nat
  AllDerive(grammar, Grammar.splitNonterminals(grammar, table, s, left, right), Lemma.slice(inputTokens, s, Nat.add(left, right)))

def split_sound(grammar, inputTokens, table, cells, s, left, right):
  match left:
    case 0n:
      Unit{}
    case 1n+(+smaller):
      +k = {1n+smaller : Nat}
      +lefts = Grammar.lookup(table, s, k)
      +rights = Grammar.lookup(table, Nat.add(s, k), right)
      here = all_derive_at(
        grammar,
        Grammar.binaryNonterminals(grammar, lefts, rights),
        List.append(&2, Nat, Lemma.slice(inputTokens, s, k), Lemma.slice(inputTokens, Nat.add(s, k), right)),
        Lemma.slice(inputTokens, s, Nat.add(k, right)),
        Lemma.slice_split(inputTokens, s, k, right),
        binary_nts_sound(
          grammar, lefts, rights,
          Lemma.slice(inputTokens, s, k), Lemma.slice(inputTokens, Nat.add(s, k), right),
          lookup_sound(grammar, inputTokens, s, k, table, cells),
          lookup_sound(grammar, inputTokens, Nat.add(s, k), right, table, cells),
          grammar, 0n, {==}))
      later = all_derive_at(
        grammar,
        Grammar.splitNonterminals(grammar, table, s, smaller, 1n+right),
        Lemma.slice(inputTokens, s, Nat.add(smaller, 1n+right)),
        Lemma.slice(inputTokens, s, 1n+Nat.add(smaller, right)),
        Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, s, n), Nat.add(smaller, 1n+right), 1n+Nat.add(smaller, right), Lemma.add_succ_right(smaller, right)),
        split_sound(grammar, inputTokens, table, cells, s, smaller, 1n+right))
      all_derive_append(grammar, Lemma.slice(inputTokens, s, Nat.add(k, right)), Grammar.binaryNonterminals(grammar, lefts, rights), Grammar.splitNonterminals(grammar, table, s, smaller, 1n+right), here, later)



law token_cell_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for token: Maybe<&2, Nat>
  for tokenEq: {List.get(&2, Nat, inputTokens, s) == token : Maybe<&2, Nat>}
  AllDerive(grammar, Grammar.tokenNonterminals(grammar, token), Lemma.slice(inputTokens, s, 1n))

def token_cell_sound(grammar, inputTokens, s, token, tokenEq):
  match token:
    case None{}:
      Unit{}
    case Some{+kind}:
      all_derive_at(
        grammar, Grammar.terminalNonterminals(grammar, kind), [kind], Lemma.slice(inputTokens, s, 1n),
        Equal.sym(+List<Nat>, Lemma.slice(inputTokens, s, 1n), [kind], Lemma.get_slice(inputTokens, s, kind, tokenEq)),
        terminal_nts_sound(grammar, kind, grammar, 0n, {==}))



law cell_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +cells: CellsSound(grammar, inputTokens, table)
  for +s: Nat
  for length: Nat
  AllDerive(grammar, Grammar.cellNonterminals(grammar, inputTokens, table, s, length), Lemma.slice(inputTokens, s, length))

def cell_sound(grammar, inputTokens, table, cells, s, length):
  match length:
    case 0n:
      Unit{}
    case 1n+0n:
      token_cell_sound(grammar, inputTokens, s, List.get(&2, Nat, inputTokens, s), {==})
    case 1n+1n+(+shorter):
      all_derive_at(
        grammar,
        Grammar.splitNonterminals(grammar, table, s, 1n+shorter, 1n),
        Lemma.slice(inputTokens, s, Nat.add(1n+shorter, 1n)),
        Lemma.slice(inputTokens, s, 1n+1n+shorter),
        Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, s, 1n+n), Nat.add(shorter, 1n), 1n+shorter, Lemma.add_one_right(shorter)),
        split_sound(grammar, inputTokens, table, cells, s, 1n+shorter, 1n))



law row_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +cells: CellsSound(grammar, inputTokens, table)
  for +length: Nat
  for remaining: Nat
  CellsSound(grammar, inputTokens, Grammar.row(grammar, inputTokens, table, length, remaining))

def row_sound(grammar, inputTokens, table, cells, length, remaining):
  match remaining:
    case 0n:
      Unit{}
    case 1n+(+start):
      (cell_sound(grammar, inputTokens, table, cells, start, length), row_sound(grammar, inputTokens, table, cells, length, start))



law cells_append:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for xs: +List<Grammar.Cell>
  for -ys: +List<Grammar.Cell>
  for first: CellsSound(grammar, inputTokens, xs)
  for second: CellsSound(grammar, inputTokens, ys)
  CellsSound(grammar, inputTokens, List.append(&2, Grammar.Cell, xs, ys))

def cells_append(grammar, inputTokens, xs, ys, first, second):
  match xs:
    case Nil{}:
      second
    case Con{Grammar.Cell{start, length, nts}, rest}:
      match first:
        case (here, later):
          (here, cells_append(grammar, inputTokens, rest, ys, later, second))



# The whole table is sound.
law table_sound:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +count: Nat
  for fuel: Nat
  CellsSound(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, count, fuel))

def table_sound(grammar, inputTokens, count, fuel):
  match fuel:
    case 0n:
      Unit{}
    case 1n+(+shorter):
      +shorterCells = table_sound(grammar, inputTokens, count, shorter)
      cells_append(
        grammar, inputTokens,
        Grammar.row(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, count, shorter), 1n+shorter, count),
        Grammar.buildTable(grammar, inputTokens, count, shorter),
        row_sound(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, count, shorter), shorterCells, 1n+shorter, count),
        shorterCells)



# ---- Soundness ----

law finish_sound:
  for -grammar: +List<Types.Production>
  for -start: Nat
  for +inputTokens: +List<Nat>
  for found: NtDerives(grammar, start, Lemma.takeN(List.length(&2, Nat, inputTokens), inputTokens))
  GrammarLaws.Derives(grammar, [Types.Nonterminal{start}], inputTokens)

def finish_sound(grammar, start, inputTokens, found):
  match found:
    case (tree, (fitting, spelled)):
      ([tree], (fitting, Equal.trans(+List<Nat>, GrammarLaws.leaves([tree]), Lemma.takeN(List.length(&2, Nat, inputTokens), inputTokens), inputTokens, spelled, Lemma.take_length(inputTokens))))



def GrammarLaws.recognize_only_derivable(grammar, start, inputTokens, accepted):
  +count = List.length(&2, Nat, inputTokens)
  +table = Grammar.buildTable(grammar, inputTokens, count, count)
  finish_sound(
    grammar, start, inputTokens,
    member_sound(
      grammar, Lemma.slice(inputTokens, 0n, count), start, Grammar.lookup(table, 0n, count), accepted,
      lookup_sound(grammar, inputTokens, 0n, count, table, table_sound(grammar, inputTokens, count, count))))



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
  for lhsOk: {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool}
  for rhsOk: {GrammarLaws.rhsOf(grammar, index) == [Types.Terminal{kind}] : +List<Types.Symbol>}
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
  for lhsOk: {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool}
  for rhsOk: {GrammarLaws.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
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
  Either<&k: Nat -> {GrammarLaws.rhsOf(grammar, index) == [Types.Terminal{k}] : +List<Types.Symbol>}, &b: Nat -> &c: Nat -> {GrammarLaws.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}>



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
  for lhsOk: {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool}
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
      inner = Lemma.and_true_right_side(GrammarLaws.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)), both)
      Lemma.and_true_intro(
        GrammarLaws.lhsIs(grammar, index, id),
        Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), True{}),
        Lemma.and_true_left(GrammarLaws.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)), both),
        Lemma.and_true_intro(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), True{}, Lemma.and_true_left(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss), inner), {==}))



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
        GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)),
        GrammarLaws.fits(ts, grammar, ss),
        Lemma.and_true_right_side(GrammarLaws.lhsIs(grammar, index, id), Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), GrammarLaws.fits(ts, grammar, ss)), e))



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
  {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool}

def node_lhs(grammar, index, a, children, fitting):
  Lemma.and_true_left(GrammarLaws.lhsIs(grammar, index, a), Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), True{}), fitting)



law node_children:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +children: +List<Types.Tree>
  for fitting: {GrammarLaws.fits([Types.Node{index, children}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  {GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)) == True{} : Bool}

def node_children(grammar, index, a, children, fitting):
  Lemma.and_true_left(
    GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)),
    True{},
    Lemma.and_true_right_side(GrammarLaws.lhsIs(grammar, index, a), Bool.and(GrammarLaws.fits(children, grammar, GrammarLaws.rhsOf(grammar, index)), True{}), fitting))



law no_children_pick:
  for -grammar: +List<Types.Production>
  for -index: Nat
  for shape: RhsShape(grammar, index)
  for childFit: {GrammarLaws.fits([], grammar, GrammarLaws.rhsOf(grammar, index)) == True{} : Bool}
  Empty

def no_children_pick(grammar, index, shape, childFit):
  match shape:
    case Inl{(k, e)}:
      Lemma.false_is_not_true(fits_at([], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit))
    case Inr{(b, (c, e))}:
      Lemma.false_is_not_true(fits_at([], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit))



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
  &kind: Nat -> {child == Types.Leaf{kind} : Types.Tree} & {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool} & {GrammarLaws.rhsOf(grammar, index) == [Types.Terminal{kind}] : +List<Types.Symbol>}



law one_child_pick:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for child: Types.Tree
  for shape: RhsShape(grammar, index)
  for lhsOk: {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool}
  for childFit: {GrammarLaws.fits([child], grammar, GrammarLaws.rhsOf(grammar, index)) == True{} : Bool}
  OneChild(grammar, index, a, child)

def one_child_pick(grammar, index, a, child, shape, lhsOk, childFit):
  match child:
    case Types.Leaf{+kind}:
      match shape:
        case Inl{(k0, e0)}:
          +k = {k0 : Nat}
          +e = {e0 : {GrammarLaws.rhsOf(grammar, index) == [Types.Terminal{k}] : +List<Types.Symbol>}}
          fitsK = fits_at([Types.Leaf{kind}], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit)
          kindIsK = Lemma.nat_eq_sound(kind, k, Lemma.and_true_left(Nat.is_eq(kind, k), True{}, fitsK))
          (kind, ({==}, (lhsOk, Equal.trans(+List<Types.Symbol>, GrammarLaws.rhsOf(grammar, index), [Types.Terminal{k}], [Types.Terminal{kind}], e, Equal.cong(Nat, +List<Types.Symbol>, n => [Types.Terminal{n}], k, kind, Equal.sym(Nat, kind, k, kindIsK))))))
        case Inr{(b, (c, e))}:
          Empty.absurd(OneChild(grammar, index, a, Types.Leaf{kind}), Lemma.false_is_not_true(fits_at([Types.Leaf{kind}], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit)))
    case Types.Node{+i, +children}:
      match shape:
        case Inl{(k, e)}:
          Empty.absurd(OneChild(grammar, index, a, Types.Node{i, children}), Lemma.false_is_not_true(fits_at([Types.Node{i, children}], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit)))
        case Inr{(b0, (c0, e))}:
          +b = {b0 : Nat}
          +c = {c0 : Nat}
          Empty.absurd(OneChild(grammar, index, a, Types.Node{i, children}), Lemma.false_is_not_true(fits_cons_right(Types.Node{i, children}, [], Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fits_at([Types.Node{i, children}], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit))))



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
  &b: Nat -> &c: Nat -> {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool} & {GrammarLaws.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>} & {GrammarLaws.fits([first], grammar, [Types.Nonterminal{b}]) == True{} : Bool} & {GrammarLaws.fits([second], grammar, [Types.Nonterminal{c}]) == True{} : Bool}



law two_children_pick:
  for +grammar: +List<Types.Production>
  for +index: Nat
  for +a: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for shape: RhsShape(grammar, index)
  for lhsOk: {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool}
  for childFit: {GrammarLaws.fits([first, second], grammar, GrammarLaws.rhsOf(grammar, index)) == True{} : Bool}
  TwoChildren(grammar, index, a, first, second)

def two_children_pick(grammar, index, a, first, second, shape, lhsOk, childFit):
  match shape:
    case Inl{(k0, e)}:
      +k = {k0 : Nat}
      fitsK = fits_at([first, second], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit)
      restFits = fits_cons_right(first, [second], Types.Terminal{k}, [], grammar, fitsK)
      Empty.absurd(TwoChildren(grammar, index, a, first, second), trees_cons_is_not_nil(second, [], GrammarLaws.only_empty_fits_nothing([second], grammar, restFits)))
    case Inr{(b0, (c0, e0))}:
      +b = {b0 : Nat}
      +c = {c0 : Nat}
      +e = {e0 : {GrammarLaws.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}}
      +fitsBC = fits_at([first, second], grammar, GrammarLaws.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit)
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
  for childFit: {GrammarLaws.fits(t1 <> t2 <> t3 <> more, grammar, GrammarLaws.rhsOf(grammar, index)) == True{} : Bool}
  Empty

def many_children_pick(grammar, index, t1, t2, t3, more, shape, childFit):
  match shape:
    case Inl{(k0, e)}:
      +k = {k0 : Nat}
      restFits = fits_cons_right(t1, t2 <> t3 <> more, Types.Terminal{k}, [], grammar, fits_at(t1 <> t2 <> t3 <> more, grammar, GrammarLaws.rhsOf(grammar, index), [Types.Terminal{k}], e, childFit))
      trees_cons_is_not_nil(t2, t3 <> more, GrammarLaws.only_empty_fits_nothing(t2 <> t3 <> more, grammar, restFits))
    case Inr{(b0, (c0, e))}:
      +b = {b0 : Nat}
      +c = {c0 : Nat}
      afterFirst = fits_cons_right(t1, t2 <> t3 <> more, Types.Nonterminal{b}, [Types.Nonterminal{c}], grammar, fits_at(t1 <> t2 <> t3 <> more, grammar, GrammarLaws.rhsOf(grammar, index), [Types.Nonterminal{b}, Types.Nonterminal{c}], e, childFit))
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
  for lhsOk: {GrammarLaws.lhsIs(grammar, index, a) == True{} : Bool}
  for rhsOk: {GrammarLaws.rhsOf(grammar, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
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



# ---- Completeness ----

law finish_complete:
  for +grammar: +List<Types.Production>
  for +start: Nat
  for +inputTokens: +List<Nat>
  for +binary: {GrammarLaws.IsBinaryForm(grammar) == True{} : Bool}
  for forest: +List<Types.Tree>
  for fitting: {GrammarLaws.fits(forest, grammar, [Types.Nonterminal{start}]) == True{} : Bool}
  for spelled: {GrammarLaws.leaves(forest) == inputTokens : +List<Nat>}
  {Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}

def finish_complete(grammar, start, inputTokens, binary, forest, fitting, spelled):
  match forest:
    case Nil{}:
      Empty.absurd({Grammar.recognize(grammar, start, inputTokens) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Con{+t, +ts}:
      +bothFit = fitting
      tsEmpty = GrammarLaws.only_empty_fits_nothing(ts, grammar, fits_cons_right(t, ts, Types.Nonterminal{start}, [], grammar, bothFit))
      +leavesT = Equal.trans(+List<Nat>, GrammarLaws.leaves([t]), GrammarLaws.leaves(t <> ts), inputTokens, Equal.cong(+List<Types.Tree>, +List<Nat>, x => GrammarLaws.leaves(t <> x), [], ts, Equal.sym(+List<Types.Tree>, ts, [], tsEmpty)), spelled)
      +count = List.length(&2, Nat, inputTokens)
      cell_complete(
        t, grammar, inputTokens, binary, start, 0n, count, count,
        fits_cons_left(t, ts, Types.Nonterminal{start}, [], grammar, bothFit),
        Equal.trans(+List<Nat>, Lemma.takeN(count, inputTokens), inputTokens, GrammarLaws.leaves([t]), Lemma.take_length(inputTokens), Equal.sym(+List<Nat>, GrammarLaws.leaves([t]), inputTokens, leavesT)),
        Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([t]), inputTokens, leavesT),
        Lemma.le_refl(count))



def GrammarLaws.recognize_every_derivable(grammar, start, inputTokens, binary, derivation):
  match derivation:
    case (forest, (fitting, spelled)):
      finish_complete(grammar, start, inputTokens, binary, forest, fitting, spelled)


# ======== BINARY SUBTREE SETS: SOUNDNESS ========

# ---- Every element of the set is a correct step ----
#
# Only leaf steps carry information about the input: Bsr{p, i, i, i + 1} says that
# production p is A = "t" and the token at i is t. Steps with another pivot are
# checked through the tree's children.

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


def stepOk(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, element: Types.Bsr) -> Bool:
  match element:
    case Types.Bsr{p, +i, k, j}:
      Bool.or(Bool.not(Nat.is_eq(k, i)), Bool.and(Nat.is_eq(j, 1n+i), tokenMatches(GrammarLaws.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))))


def allOk(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, set: +List<Types.Bsr>) -> Bool:
  match set:
    case Nil{}:
      True{}
    case Con{element, rest}:
      Bool.and(stepOk(grammar, inputTokens, element), allOk(grammar, inputTokens, rest))


law ok_append:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for xs: +List<Types.Bsr>
  for -ys: +List<Types.Bsr>
  for first: {allOk(grammar, inputTokens, xs) == True{} : Bool}
  for second: {allOk(grammar, inputTokens, ys) == True{} : Bool}
  {allOk(grammar, inputTokens, List.append(&2, Types.Bsr, xs, ys)) == True{} : Bool}

def ok_append(grammar, inputTokens, xs, ys, first, second):
  match xs:
    case Nil{}:
      second
    case Con{+element, +rest}:
      +both = first
      Lemma.and_true_intro(
        stepOk(grammar, inputTokens, element),
        allOk(grammar, inputTokens, List.append(&2, Types.Bsr, rest, ys)),
        Lemma.and_true_left(stepOk(grammar, inputTokens, element), allOk(grammar, inputTokens, rest), both),
        ok_append(grammar, inputTokens, rest, ys, Lemma.and_true_right_side(stepOk(grammar, inputTokens, element), allOk(grammar, inputTokens, rest), both), second))


law ok_keep:
  for keep: Bool
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +element: Types.Bsr
  for -rest: +List<Types.Bsr>
  for elementOk: {Bool.or(Bool.not(keep), stepOk(grammar, inputTokens, element)) == True{} : Bool}
  for restOk: {allOk(grammar, inputTokens, rest) == True{} : Bool}
  {allOk(grammar, inputTokens, Grammar.keepBsr(keep, element, rest)) == True{} : Bool}

def ok_keep(keep, grammar, inputTokens, element, rest, elementOk, restOk):
  match keep:
    case False{}:
      restOk
    case True{}:
      Lemma.and_true_intro(stepOk(grammar, inputTokens, element), allOk(grammar, inputTokens, rest), elementOk, restOk)


# A step whose pivot is after its start is always fine.
law binary_step_ok:
  for -grammar: +List<Types.Production>
  for -inputTokens: +List<Nat>
  for -index: Nat
  for +i: Nat
  for +n: Nat
  for -j: Nat
  {stepOk(grammar, inputTokens, Types.Bsr{index, i, Nat.add(i, 1n+n), j}) == True{} : Bool}

def binary_step_ok(grammar, inputTokens, index, i, n, j):
  %Equal.sym(Bool, Nat.is_eq(Nat.add(i, 1n+n), i), False{}, Lemma.add_succ_ne(i, n)) : {Bool.or(Bool.not(_), Bool.and(Nat.is_eq(j, 1n+i), tokenMatches(GrammarLaws.rhsOf(grammar, index), List.get(&2, Nat, inputTokens, i)))) == True{} : Bool}
  {==}


# A leaf step is fine when the token at s is the production's terminal.
law leaf_step_ok:
  for -grammar: +List<Types.Production>
  for -inputTokens: +List<Nat>
  for -index: Nat
  for +s: Nat
  for matches: {tokenMatches(GrammarLaws.rhsOf(grammar, index), List.get(&2, Nat, inputTokens, s)) == True{} : Bool}
  {stepOk(grammar, inputTokens, Types.Bsr{index, s, s, 1n+s}) == True{} : Bool}

def leaf_step_ok(grammar, inputTokens, index, s, matches):
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, Lemma.nat_eq_refl(s)) : {Bool.or(Bool.not(_), Bool.and(_, tokenMatches(GrammarLaws.rhsOf(grammar, index), List.get(&2, Nat, inputTokens, s)))) == True{} : Bool}
  matches


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
  {tokenMatches(GrammarLaws.rhsOf(grammar, o), List.get(&2, Nat, inputTokens, s)) == True{} : Bool}

def leaf_matches(grammar, inputTokens, kind, s, lhs, k, others, o, keptEq, tokenEq, tail):
  %Equal.sym(+List<Types.Symbol>, GrammarLaws.rhsOf(grammar, o), [Types.Terminal{k}], rhs_at(grammar, o, lhs, [Types.Terminal{k}], others, tail)) : {tokenMatches(_, List.get(&2, Nat, inputTokens, s)) == True{} : Bool}
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, inputTokens, s), Some{kind}, tokenEq) : {tokenMatches([Types.Terminal{k}], _) == True{} : Bool}
  keptEq


law keep_leaf_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
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
  for later: {allOk(grammar, inputTokens, Grammar.terminalSteps(others, kind, s, 1n+o)) == True{} : Bool}
  {allOk(grammar, inputTokens, Grammar.keepBsr(keep, Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))) == True{} : Bool}

def keep_leaf_ok(grammar, inputTokens, kind, s, lhs, k, others, o, keep, keptEq, tokenEq, tail, later):
  match keep:
    case False{}:
      later
    case True{}:
      matches = leaf_matches(grammar, inputTokens, kind, s, lhs, k, others, o, keptEq, tokenEq, tail)
      Lemma.and_true_intro(stepOk(grammar, inputTokens, Types.Bsr{o, s, s, 1n+s}), allOk(grammar, inputTokens, Grammar.terminalSteps(others, kind, s, 1n+o)), leaf_step_ok(grammar, inputTokens, o, s, matches), later)


law terminal_steps_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +kind: Nat
  for +s: Nat
  for +tokenEq: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  for rest: +List<Types.Production>
  for +o: Nat
  for +tail: {dropP(o, grammar) == rest : +List<Types.Production>}
  {allOk(grammar, inputTokens, Grammar.terminalSteps(rest, kind, s, o)) == True{} : Bool}

def terminal_steps_ok(grammar, inputTokens, kind, s, tokenEq, rest, o, tail):
  match rest:
    case Nil{}:
      {==}
    case Con{Types.Production{+lhs, [Types.Terminal{+k}]}, +others}:
      keep_leaf_ok(
        grammar, inputTokens, kind, s, lhs, k, others, o,
        Nat.is_eq(k, kind), {==}, tokenEq, tail,
        terminal_steps_ok(grammar, inputTokens, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, [Types.Terminal{k}]}, others, tail)))
    case Con{Types.Production{+lhs, Nil{}}, +others}:
      terminal_steps_ok(grammar, inputTokens, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, []}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Terminal{+k}, Con{+second, +more}}}, +others}:
      terminal_steps_ok(grammar, inputTokens, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Terminal{k} <> second <> more}, others, tail))
    case Con{Types.Production{+lhs, Con{Types.Nonterminal{+first}, +more}}, +others}:
      terminal_steps_ok(grammar, inputTokens, kind, s, tokenEq, others, 1n+o, drop_next(grammar, o, Types.Production{lhs, Types.Nonterminal{first} <> more}, others, tail))


law binary_steps_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +lefts: +List<Nat>
  for +rights: +List<Nat>
  for +i: Nat
  for +n: Nat
  for +j: Nat
  for rest: +List<Types.Production>
  for +o: Nat
  {allOk(grammar, inputTokens, Grammar.binarySteps(rest, lefts, rights, i, Nat.add(i, 1n+n), j, o)) == True{} : Bool}

def binary_steps_ok(grammar, inputTokens, lefts, rights, i, n, j, rest, o):
  match rest:
    case Nil{}:
      {==}
    case Con{Types.Production{lhs, [Types.Nonterminal{+b}, Types.Nonterminal{+c}]}, +others}:
      ok_keep(
        Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)),
        grammar, inputTokens, Types.Bsr{o, i, Nat.add(i, 1n+n), j}, Grammar.binarySteps(others, lefts, rights, i, Nat.add(i, 1n+n), j, 1n+o),
        Lemma.or_true_right_intro(Bool.not(Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights))), stepOk(grammar, inputTokens, Types.Bsr{o, i, Nat.add(i, 1n+n), j}), binary_step_ok(grammar, inputTokens, o, i, n, j)),
        binary_steps_ok(grammar, inputTokens, lefts, rights, i, n, j, others, 1n+o))
    case Con{Types.Production{lhs, Nil{}}, +others}:
      binary_steps_ok(grammar, inputTokens, lefts, rights, i, n, j, others, 1n+o)
    case Con{Types.Production{lhs, Con{Types.Terminal{k}, more}}, +others}:
      binary_steps_ok(grammar, inputTokens, lefts, rights, i, n, j, others, 1n+o)
    case Con{Types.Production{lhs, Con{Types.Nonterminal{b}, Nil{}}}, +others}:
      binary_steps_ok(grammar, inputTokens, lefts, rights, i, n, j, others, 1n+o)
    case Con{Types.Production{lhs, Con{Types.Nonterminal{b}, Con{Types.Terminal{k}, more}}}, +others}:
      binary_steps_ok(grammar, inputTokens, lefts, rights, i, n, j, others, 1n+o)
    case Con{Types.Production{lhs, Con{Types.Nonterminal{b}, Con{Types.Nonterminal{c}, Con{x, more}}}}, +others}:
      binary_steps_ok(grammar, inputTokens, lefts, rights, i, n, j, others, 1n+o)


law token_steps_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for token: Maybe<&2, Nat>
  for tokenEq: {List.get(&2, Nat, inputTokens, s) == token : Maybe<&2, Nat>}
  {allOk(grammar, inputTokens, Grammar.tokenSteps(grammar, token, s)) == True{} : Bool}

def token_steps_ok(grammar, inputTokens, s, token, tokenEq):
  match token:
    case None{}:
      {==}
    case Some{+kind}:
      terminal_steps_ok(grammar, inputTokens, kind, s, tokenEq, grammar, 0n, {==})


law split_steps_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for left: Nat
  for +right: Nat
  {allOk(grammar, inputTokens, Grammar.splitSteps(grammar, table, s, left, right)) == True{} : Bool}

def split_steps_ok(grammar, inputTokens, table, s, left, right):
  match left:
    case 0n:
      {==}
    case 1n+(+smaller):
      ok_append(
        grammar, inputTokens,
        Grammar.binarySteps(grammar, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), right), s, Nat.add(s, 1n+smaller), Nat.add(s, Nat.add(1n+smaller, right)), 0n),
        Grammar.splitSteps(grammar, table, s, smaller, 1n+right),
        binary_steps_ok(grammar, inputTokens, Grammar.lookup(table, s, 1n+smaller), Grammar.lookup(table, Nat.add(s, 1n+smaller), right), s, smaller, Nat.add(s, Nat.add(1n+smaller, right)), grammar, 0n),
        split_steps_ok(grammar, inputTokens, table, s, smaller, 1n+right))


law span_steps_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +s: Nat
  for length: Nat
  {allOk(grammar, inputTokens, Grammar.spanSteps(grammar, inputTokens, table, s, length)) == True{} : Bool}

def span_steps_ok(grammar, inputTokens, table, s, length):
  match length:
    case 0n:
      {==}
    case 1n+0n:
      token_steps_ok(grammar, inputTokens, s, List.get(&2, Nat, inputTokens, s), {==})
    case 1n+1n+(+shorter):
      split_steps_ok(grammar, inputTokens, table, s, 1n+shorter, 1n)


law row_steps_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +length: Nat
  for remaining: Nat
  {allOk(grammar, inputTokens, Grammar.rowSteps(grammar, inputTokens, table, length, remaining)) == True{} : Bool}

def row_steps_ok(grammar, inputTokens, table, length, remaining):
  match remaining:
    case 0n:
      {==}
    case 1n+(+start):
      ok_append(grammar, inputTokens, Grammar.spanSteps(grammar, inputTokens, table, start, length), Grammar.rowSteps(grammar, inputTokens, table, length, start), span_steps_ok(grammar, inputTokens, table, start, length), row_steps_ok(grammar, inputTokens, table, length, start))


law all_steps_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +table: +List<Grammar.Cell>
  for +count: Nat
  for fuel: Nat
  {allOk(grammar, inputTokens, Grammar.allSteps(grammar, inputTokens, table, count, fuel)) == True{} : Bool}

def all_steps_ok(grammar, inputTokens, table, count, fuel):
  match fuel:
    case 0n:
      {==}
    case 1n+(+shorter):
      ok_append(grammar, inputTokens, Grammar.rowSteps(grammar, inputTokens, table, 1n+shorter, count), Grammar.allSteps(grammar, inputTokens, table, count, shorter), row_steps_ok(grammar, inputTokens, table, 1n+shorter, count), all_steps_ok(grammar, inputTokens, table, count, shorter))


# Every element of the BSR set is a correct step.
law set_ok:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  {allOk(grammar, inputTokens, Grammar.bsrSet(grammar, inputTokens)) == True{} : Bool}

def set_ok(grammar, inputTokens):
  +count = List.length(&2, Nat, inputTokens)
  all_steps_ok(grammar, inputTokens, Grammar.buildTable(grammar, inputTokens, count, count), count, count)


# ---- Members of a correct set are correct steps ----

law member_ok_pick:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  for +p2: Nat
  for +i2: Nat
  for +k2: Nat
  for +j2: Nat
  for -rest: +List<Types.Bsr>
  for cases: Either<{Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))) == True{} : Bool}, {GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, rest) == True{} : Bool}>
  for headOk: {stepOk(grammar, inputTokens, Types.Bsr{p2, i2, k2, j2}) == True{} : Bool}
  for searchRest: {GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, rest) == True{} : Bool} -> {stepOk(grammar, inputTokens, Types.Bsr{p, i, k, j}) == True{} : Bool}
  {stepOk(grammar, inputTokens, Types.Bsr{p, i, k, j}) == True{} : Bool}

def member_ok_pick(grammar, inputTokens, p, i, k, j, p2, i2, k2, j2, rest, cases, headOk, searchRest):
  match cases:
    case Inl{same}:
      +all = same
      +ikj = Lemma.and_true_right_side(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), all)
      +kj = Lemma.and_true_right_side(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), ikj)
      samePosition = Lemma.nat_eq_sound(p, p2, Lemma.and_true_left(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))), all))
      sameStart = Lemma.nat_eq_sound(i, i2, Lemma.and_true_left(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)), ikj))
      samePivot = Lemma.nat_eq_sound(k, k2, Lemma.and_true_left(Nat.is_eq(k, k2), Nat.is_eq(j, j2), kj))
      sameEnd = Lemma.nat_eq_sound(j, j2, Lemma.and_true_right_side(Nat.is_eq(k, k2), Nat.is_eq(j, j2), kj))
      %Equal.sym(Nat, p, p2, samePosition) : {stepOk(grammar, inputTokens, Types.Bsr{_, i, k, j}) == True{} : Bool}
      %Equal.sym(Nat, i, i2, sameStart) : {stepOk(grammar, inputTokens, Types.Bsr{p2, _, k, j}) == True{} : Bool}
      %Equal.sym(Nat, k, k2, samePivot) : {stepOk(grammar, inputTokens, Types.Bsr{p2, i2, _, j}) == True{} : Bool}
      %Equal.sym(Nat, j, j2, sameEnd) : {stepOk(grammar, inputTokens, Types.Bsr{p2, i2, k2, _}) == True{} : Bool}
      headOk
    case Inr{inRest}:
      searchRest(inRest)


law ok_member:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for element: Types.Bsr
  for set: +List<Types.Bsr>
  for m: {GrammarLaws.bsrMember(element, set) == True{} : Bool}
  for +ok: {allOk(grammar, inputTokens, set) == True{} : Bool}
  {stepOk(grammar, inputTokens, element) == True{} : Bool}

def ok_member(grammar, inputTokens, element, set, m, ok):
  match element:
    case Types.Bsr{+p, +i, +k, +j}:
      match set:
        case Nil{}:
          Empty.absurd({stepOk(grammar, inputTokens, Types.Bsr{p, i, k, j}) == True{} : Bool}, Lemma.false_is_not_true(m))
        case Con{Types.Bsr{+p2, +i2, +k2, +j2}, +rest}:
          member_ok_pick(
            grammar, inputTokens, p, i, k, j, p2, i2, k2, j2, rest,
            Lemma.or_true_cases(Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, rest), m),
            Lemma.and_true_left(stepOk(grammar, inputTokens, Types.Bsr{p2, i2, k2, j2}), allOk(grammar, inputTokens, rest), ok),
            inRest => ok_member(grammar, inputTokens, Types.Bsr{p, i, k, j}, rest, inRest, Lemma.and_true_right_side(stepOk(grammar, inputTokens, Types.Bsr{p2, i2, k2, j2}), allOk(grammar, inputTokens, rest), ok)))


# A correct leaf step: the production's right side matches the token at i.
law leaf_matches_token:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +p: Nat
  for +i: Nat
  for e: {stepOk(grammar, inputTokens, Types.Bsr{p, i, i, 1n+i}) == True{} : Bool}
  {tokenMatches(GrammarLaws.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i)) == True{} : Bool}

def leaf_matches_token(grammar, inputTokens, p, i, e):
  +tm = tokenMatches(GrammarLaws.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))
  Lemma.and_true_right_side(
    Nat.is_eq(1n+i, 1n+i), tm,
    Lemma.or_false_left(Bool.not(Nat.is_eq(i, i)), Bool.and(Nat.is_eq(1n+i, 1n+i), tm), Equal.cong(Bool, Bool, b => Bool.not(b), Nat.is_eq(i, i), True{}, Lemma.nat_eq_refl(i)), e))


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


# Two trees that fit a right side: it has exactly two symbols, one per tree.
def TwoFit(+grammar: +List<Types.Production>, +rhs: +List<Types.Symbol>, +first: Types.Tree, +second: Types.Tree) -> Type:
  &s1: Types.Symbol -> &s2: Types.Symbol -> {rhs == [s1, s2] : +List<Types.Symbol>} & {GrammarLaws.fits([first], grammar, [s1]) == True{} : Bool} & {GrammarLaws.fits([second], grammar, [s2]) == True{} : Bool}


law fits_two:
  for rhs: +List<Types.Symbol>
  for +first: Types.Tree
  for +second: Types.Tree
  for +grammar: +List<Types.Production>
  for +e: {GrammarLaws.fits([first, second], grammar, rhs) == True{} : Bool}
  TwoFit(grammar, rhs, first, second)

def fits_two(rhs, first, second, grammar, e):
  match rhs:
    case Nil{}:
      match first:
        case Types.Leaf{kind}:
          Empty.absurd(TwoFit(grammar, [], Types.Leaf{kind}, second), Lemma.false_is_not_true(e))
        case Types.Node{index, children}:
          Empty.absurd(TwoFit(grammar, [], Types.Node{index, children}, second), Lemma.false_is_not_true(e))
    case Con{+s1, Nil{}}:
      rest = fits_cons_right(first, [second], s1, [], grammar, e)
      Empty.absurd(TwoFit(grammar, [s1], first, second), trees_cons_is_not_nil(second, [], GrammarLaws.only_empty_fits_nothing([second], grammar, rest)))
    case Con{+s1, Con{+s2, Nil{}}}:
      (s1, (s2, ({==}, (fits_cons_left(first, [second], s1, [s2], grammar, e), fits_cons_right(first, [second], s1, [s2], grammar, e)))))
    case Con{+s1, Con{+s2, Con{+s3, +more}}}:
      afterFirst = fits_cons_right(first, [second], s1, s2 <> s3 <> more, grammar, e)
      afterSecond = fits_cons_right(second, [], s2, s3 <> more, grammar, afterFirst)
      Empty.absurd(TwoFit(grammar, s1 <> s2 <> s3 <> more, first, second), Lemma.false_is_not_true(afterSecond))


# ---- A fitting tree embedded in a correct set spells the input ----

# Spells(t, input, i): the leaves of t are the input from position i on.
def Spells(+tree: Types.Tree, +inputTokens: +List<Nat>, +i: Nat) -> Type:
  {GrammarLaws.leaves([tree]) == Lemma.slice(inputTokens, i, List.length(&2, Nat, GrammarLaws.leaves([tree]))) : +List<Nat>}


law leaf_spells_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +i: Nat
  for +p: Nat
  for +a: Nat
  for +kind: Nat
  for fitting: {GrammarLaws.fits([Types.Node{p, [Types.Leaf{kind}]}], grammar, [Types.Nonterminal{a}]) == True{} : Bool}
  for parts: TokenParts(GrammarLaws.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i))
  Spells(Types.Node{p, [Types.Leaf{kind}]}, inputTokens, i)

def leaf_spells_parts(grammar, inputTokens, i, p, a, kind, fitting, parts):
  match parts:
    case (+k, (rhsEq, +tokenEq)):
      childFits = fits_at([Types.Leaf{kind}], grammar, GrammarLaws.rhsOf(grammar, p), [Types.Terminal{k}], rhsEq, node_children(grammar, p, a, [Types.Leaf{kind}], fitting))
      kindIsK = Lemma.nat_eq_sound(kind, k, Lemma.and_true_left(Nat.is_eq(kind, k), True{}, childFits))
      Equal.trans(+List<Nat>, [kind], [k], Lemma.slice(inputTokens, i, 1n), Equal.cong(Nat, +List<Nat>, n => [n], kind, k, kindIsK), Equal.sym(+List<Nat>, Lemma.slice(inputTokens, i, 1n), [k], Lemma.get_slice(inputTokens, i, k, tokenEq)))


law pair_spells_parts:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +set: +List<Types.Bsr>
  for +i: Nat
  for +p: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for +inSet: {GrammarLaws.embedded(Types.Node{p, [first, second]}, set, i) == True{} : Bool}
  for parts: TwoFit(grammar, GrammarLaws.rhsOf(grammar, p), first, second)
  for firstSpells: @s1: Types.Symbol -> @i1: Nat -> {GrammarLaws.fits([first], grammar, [s1]) == True{} : Bool} -> {GrammarLaws.embedded(first, set, i1) == True{} : Bool} -> Spells(first, inputTokens, i1)
  for secondSpells: @s2: Types.Symbol -> @i2: Nat -> {GrammarLaws.fits([second], grammar, [s2]) == True{} : Bool} -> {GrammarLaws.embedded(second, set, i2) == True{} : Bool} -> Spells(second, inputTokens, i2)
  Spells(Types.Node{p, [first, second]}, inputTokens, i)

def pair_spells_parts(grammar, inputTokens, set, i, p, first, second, inSet, parts, firstSpells, secondSpells):
  match parts:
    case (s1, (s2, (rhsEq, (f1, f2)))):
      +l1 = List.length(&2, Nat, GrammarLaws.leaves([first]))
      +l2 = List.length(&2, Nat, GrammarLaws.leaves([second]))
      +k = Nat.add(i, l1)
      +j = Nat.add(k, l2)
      +bothEmbedded = Lemma.and_true_right_side(GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, set), Bool.and(GrammarLaws.embedded(first, set, i), GrammarLaws.embedded(second, set, k)), inSet)
      spells1 = firstSpells(s1, i, f1, Lemma.and_true_left(GrammarLaws.embedded(first, set, i), GrammarLaws.embedded(second, set, k), bothEmbedded))
      spells2 = secondSpells(s2, k, f2, Lemma.and_true_right_side(GrammarLaws.embedded(first, set, i), GrammarLaws.embedded(second, set, k), bothEmbedded))
      +w1 = GrammarLaws.leaves([first])
      +w2 = GrammarLaws.leaves([second])
      +joined = node_leaves(p, [first, second], List.append(&2, Nat, w1, w2), pair_leaves(first, second, w1, w2, {==}, {==}))
      lengthEq = Equal.trans(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])), List.length(&2, Nat, List.append(&2, Nat, w1, w2)), Nat.add(l1, l2), Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([Types.Node{p, [first, second]}]), List.append(&2, Nat, w1, w2), joined), Lemma.length_append(w1, w2))
      Equal.trans(
        +List<Nat>,
        GrammarLaws.leaves([Types.Node{p, [first, second]}]),
        List.append(&2, Nat, w1, w2),
        Lemma.slice(inputTokens, i, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}]))),
        joined,
        Equal.trans(
          +List<Nat>,
          List.append(&2, Nat, w1, w2),
          List.append(&2, Nat, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, k, l2)),
          Lemma.slice(inputTokens, i, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}]))),
          Lemma.append_congr(w1, w2, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, k, l2), spells1, spells2),
          Equal.trans(
            +List<Nat>,
            List.append(&2, Nat, Lemma.slice(inputTokens, i, l1), Lemma.slice(inputTokens, k, l2)),
            Lemma.slice(inputTokens, i, Nat.add(l1, l2)),
            Lemma.slice(inputTokens, i, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}]))),
            Lemma.slice_split(inputTokens, i, l1, l2),
            Equal.cong(Nat, +List<Nat>, n => Lemma.slice(inputTokens, i, n), Nat.add(l1, l2), List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])), Equal.sym(Nat, List.length(&2, Nat, GrammarLaws.leaves([Types.Node{p, [first, second]}])), Nat.add(l1, l2), lengthEq)))))


law leaf_spells:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +set: +List<Types.Bsr>
  for +setOk: {allOk(grammar, inputTokens, set) == True{} : Bool}
  for symbol: Types.Symbol
  for +i: Nat
  for +p: Nat
  for +kind: Nat
  for fitting: {GrammarLaws.fits([Types.Node{p, [Types.Leaf{kind}]}], grammar, [symbol]) == True{} : Bool}
  for inSet: {GrammarLaws.bsrMember(Types.Bsr{p, i, i, 1n+i}, set) == True{} : Bool}
  Spells(Types.Node{p, [Types.Leaf{kind}]}, inputTokens, i)

def leaf_spells(grammar, inputTokens, set, setOk, symbol, i, p, kind, fitting, inSet):
  match symbol:
    case Types.Terminal{k}:
      Empty.absurd(Spells(Types.Node{p, [Types.Leaf{kind}]}, inputTokens, i), Lemma.false_is_not_true(fitting))
    case Types.Nonterminal{+a}:
      matches = leaf_matches_token(grammar, inputTokens, p, i, ok_member(grammar, inputTokens, Types.Bsr{p, i, i, 1n+i}, set, inSet, setOk))
      leaf_spells_parts(grammar, inputTokens, i, p, a, kind, fitting, token_matches_parts(GrammarLaws.rhsOf(grammar, p), List.get(&2, Nat, inputTokens, i), matches))


law pair_spells:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +set: +List<Types.Bsr>
  for symbol: Types.Symbol
  for +i: Nat
  for +p: Nat
  for +first: Types.Tree
  for +second: Types.Tree
  for fitting: {GrammarLaws.fits([Types.Node{p, [first, second]}], grammar, [symbol]) == True{} : Bool}
  for +inSet: {GrammarLaws.embedded(Types.Node{p, [first, second]}, set, i) == True{} : Bool}
  for firstSpells: @s1: Types.Symbol -> @i1: Nat -> {GrammarLaws.fits([first], grammar, [s1]) == True{} : Bool} -> {GrammarLaws.embedded(first, set, i1) == True{} : Bool} -> Spells(first, inputTokens, i1)
  for secondSpells: @s2: Types.Symbol -> @i2: Nat -> {GrammarLaws.fits([second], grammar, [s2]) == True{} : Bool} -> {GrammarLaws.embedded(second, set, i2) == True{} : Bool} -> Spells(second, inputTokens, i2)
  Spells(Types.Node{p, [first, second]}, inputTokens, i)

def pair_spells(grammar, inputTokens, set, symbol, i, p, first, second, fitting, inSet, firstSpells, secondSpells):
  match symbol:
    case Types.Terminal{k}:
      Empty.absurd(Spells(Types.Node{p, [first, second]}, inputTokens, i), Lemma.false_is_not_true(fitting))
    case Types.Nonterminal{+a}:
      pair_spells_parts(grammar, inputTokens, set, i, p, first, second, inSet, fits_two(GrammarLaws.rhsOf(grammar, p), first, second, grammar, node_children(grammar, p, a, [first, second], fitting)), firstSpells, secondSpells)


law tree_spells:
  for t: Types.Tree
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +set: +List<Types.Bsr>
  for +setOk: {allOk(grammar, inputTokens, set) == True{} : Bool}
  for symbol: Types.Symbol
  for +i: Nat
  for fitting: {GrammarLaws.fits([t], grammar, [symbol]) == True{} : Bool}
  for inSet: {GrammarLaws.embedded(t, set, i) == True{} : Bool}
  Spells(t, inputTokens, i)

def tree_spells(t, grammar, inputTokens, set, setOk, symbol, i, fitting, inSet):
  match t:
    case Types.Leaf{kind}:
      Empty.absurd(Spells(Types.Leaf{kind}, inputTokens, i), Lemma.false_is_not_true(inSet))
    case Types.Node{+p, children}:
      match children:
        case Nil{}:
          Empty.absurd(Spells(Types.Node{p, []}, inputTokens, i), Lemma.false_is_not_true(inSet))
        case Con{Types.Leaf{+kind}, Nil{}}:
          leaf_spells(grammar, inputTokens, set, setOk, symbol, i, p, kind, fitting, inSet)
        case Con{Types.Node{q, grandchildren}, Nil{}}:
          Empty.absurd(Spells(Types.Node{p, [Types.Node{q, grandchildren}]}, inputTokens, i), Lemma.false_is_not_true(inSet))
        case Con{+first, Con{+second, Nil{}}}:
          pair_spells(
            grammar, inputTokens, set, symbol, i, p, first, second, fitting, inSet,
            s1 => i1 => f1 => e1 => tree_spells(first, grammar, inputTokens, set, setOk, s1, i1, f1, e1),
            s2 => i2 => f2 => e2 => tree_spells(second, grammar, inputTokens, set, setOk, s2, i2, f2, e2))
        case Con{first, Con{second, Con{third, more}}}:
          Empty.absurd(Spells(Types.Node{p, first <> second <> third <> more}, inputTokens, i), Lemma.false_is_not_true(inSet))


# ---- Soundness ----

def GrammarLaws.bsr_only_parse_trees(grammar, start, inputTokens, tree, fitting, long, inSet):
  spelled = tree_spells(tree, grammar, inputTokens, Grammar.bsrSet(grammar, inputTokens), set_ok(grammar, inputTokens), Types.Nonterminal{start}, 0n, fitting, inSet)
  Equal.trans(
    +List<Nat>,
    GrammarLaws.leaves([tree]),
    Lemma.takeN(List.length(&2, Nat, GrammarLaws.leaves([tree])), inputTokens),
    inputTokens,
    spelled,
    Equal.trans(
      +List<Nat>,
      Lemma.takeN(List.length(&2, Nat, GrammarLaws.leaves([tree])), inputTokens),
      Lemma.takeN(List.length(&2, Nat, inputTokens), inputTokens),
      inputTokens,
      Equal.cong(Nat, +List<Nat>, n => Lemma.takeN(n, inputTokens), List.length(&2, Nat, GrammarLaws.leaves([tree])), List.length(&2, Nat, inputTokens), long),
      Lemma.take_length(inputTokens)))


# ======== BINARY SUBTREE SETS: COMPLETENESS ========

# ---- Membership in lists of steps ----

law bsr_eq_refl:
  for +p: Nat
  for +i: Nat
  for +k: Nat
  for +j: Nat
  {Bool.and(Nat.is_eq(p, p), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)))) == True{} : Bool}

def bsr_eq_refl(p, i, k, j):
  Lemma.and_true_intro(Nat.is_eq(p, p), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))), Lemma.nat_eq_refl(p),
    Lemma.and_true_intro(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)), Lemma.nat_eq_refl(i),
      Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(j, j), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(j))))


law bsr_member_head:
  for element: Types.Bsr
  for +rest: +List<Types.Bsr>
  {GrammarLaws.bsrMember(element, element <> rest) == True{} : Bool}

def bsr_member_head(element, rest):
  match element:
    case Types.Bsr{+p, +i, +k, +j}:
      Lemma.or_true_left_intro(Bool.and(Nat.is_eq(p, p), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)))), GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, rest), bsr_eq_refl(p, i, k, j))


law bsr_member_cons:
  for element: Types.Bsr
  for +x: Types.Bsr
  for +rest: +List<Types.Bsr>
  for e: {GrammarLaws.bsrMember(element, rest) == True{} : Bool}
  {GrammarLaws.bsrMember(element, x <> rest) == True{} : Bool}

def bsr_member_cons(element, x, rest, e):
  match element x:
    case Types.Bsr{+p, +i, +k, +j} Types.Bsr{p2, i2, k2, j2}:
      Lemma.or_true_right_intro(Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))), GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, rest), e)


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
    case Types.Bsr{+p, +i, +k, +j}:
      match xs:
        case Nil{}:
          Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, ys) == True{} : Bool}, Lemma.false_is_not_true(e))
        case Con{Types.Bsr{+p2, +i2, +k2, +j2}, +rest}:
          Lemma.or_mono_right(
            Bool.and(Nat.is_eq(p, p2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2)))),
            GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, rest),
            GrammarLaws.bsrMember(Types.Bsr{p, i, k, j}, List.append(&2, Types.Bsr, rest, ys)),
            e,
            inRest => bsr_member_append_left(Types.Bsr{p, i, k, j}, rest, ys, inRest))


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
  {GrammarLaws.bsrMember(Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, rhs} <> others, kind, s, o)) == True{} : Bool}

def terminal_head_member(lhs, rhs, others, kind, s, o, rhsOk):
  match rhs:
    case Con{Types.Terminal{+k}, Nil{}}:
      kIsKind = Equal.cong(+List<Types.Symbol>, Nat, l => terminalOf(l), [Types.Terminal{k}], [Types.Terminal{kind}], rhsOk)
      %Equal.sym(Nat, k, kind, kIsKind) : {GrammarLaws.bsrMember(Types.Bsr{o, s, s, 1n+s}, Grammar.keepBsr(Nat.is_eq(_, kind), Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(kind, kind), True{}, Lemma.nat_eq_refl(kind)) : {GrammarLaws.bsrMember(Types.Bsr{o, s, s, 1n+s}, Grammar.keepBsr(_, Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))) == True{} : Bool}
      bsr_member_head(Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o))
    case Nil{}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, []} <> others, kind, s, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), [], [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Terminal{k}, Con{x, more}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, Types.Terminal{k} <> x <> more} <> others, kind, s, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), Types.Terminal{k} <> x <> more, [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Nonterminal{b}, more}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, Types.Nonterminal{b} <> more} <> others, kind, s, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), Types.Nonterminal{b} <> more, [Types.Terminal{kind}], rhsOk)))


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
      bsr_member_keep(Nat.is_eq(k, kind), Types.Bsr{o, s, s, 1n+s}, Grammar.terminalSteps(others, kind, s, 1n+o), element, e)
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
  for rhsOk: {GrammarLaws.rhsOf(rest, index) == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {GrammarLaws.bsrMember(Types.Bsr{Nat.add(o, index), s, s, 1n+s}, Grammar.terminalSteps(rest, kind, s, o)) == True{} : Bool}

def terminal_steps_member(rest, kind, s, o, index, rhsOk):
  match rest index:
    case Nil{} _:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Nat.add(o, index), s, s, 1n+s}, []) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isSingleTerminal(l), [], [Types.Terminal{kind}], rhsOk)))
    case Con{Types.Production{+lhs, +rhs}, +others} 0n:
      %Equal.sym(Nat, Nat.add(o, 0n), o, Lemma.add_zero_right(o)) : {GrammarLaws.bsrMember(Types.Bsr{_, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, rhs} <> others, kind, s, o)) == True{} : Bool}
      terminal_head_member(lhs, rhs, others, kind, s, o, rhsOk)
    case Con{Types.Production{+lhs, +rhs}, +others} 1n+(+i):
      %Equal.sym(Nat, Nat.add(o, 1n+i), 1n+Nat.add(o, i), Lemma.add_succ_right(o, i)) : {GrammarLaws.bsrMember(Types.Bsr{_, s, s, 1n+s}, Grammar.terminalSteps(Types.Production{lhs, rhs} <> others, kind, s, o)) == True{} : Bool}
      terminal_steps_skip(lhs, rhs, others, kind, s, o, Types.Bsr{Nat.add(1n+o, i), s, s, 1n+s}, terminal_steps_member(others, kind, s, 1n+o, i, rhsOk))


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
  {GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.binarySteps(Types.Production{lhs, rhs} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}

def binary_head_member(lhs, rhs, others, lefts, rights, i, k, j, o, b, c, rhsOk, inLefts, inRights):
  match rhs:
    case Con{Types.Nonterminal{+b2}, Con{Types.Nonterminal{+c2}, Nil{}}}:
      +sameRhs = rhsOk
      bEq = Equal.cong(+List<Types.Symbol>, Nat, l => firstNonterminalOf(l), [Types.Nonterminal{b2}, Types.Nonterminal{c2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], sameRhs)
      cEq = Equal.cong(+List<Types.Symbol>, Nat, l => secondNonterminalOf(l), [Types.Nonterminal{b2}, Types.Nonterminal{c2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], sameRhs)
      +later = Grammar.binarySteps(others, lefts, rights, i, k, j, 1n+o)
      %Equal.sym(Nat, b2, b, bEq) : {GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.keepBsr(Bool.and(Grammar.natMember(_, lefts), Grammar.natMember(c2, rights)), Types.Bsr{o, i, k, j}, later)) == True{} : Bool}
      %Equal.sym(Nat, c2, c, cEq) : {GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.keepBsr(Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(_, rights)), Types.Bsr{o, i, k, j}, later)) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), True{}, Lemma.and_true_intro(Grammar.natMember(b, lefts), Grammar.natMember(c, rights), inLefts, inRights)) : {GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.keepBsr(_, Types.Bsr{o, i, k, j}, later)) == True{} : Bool}
      bsr_member_head(Types.Bsr{o, i, k, j}, later)
    case Nil{}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.binarySteps(Types.Production{lhs, []} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Terminal{t}, more}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.binarySteps(Types.Production{lhs, Types.Terminal{t} <> more} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Terminal{t} <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Nil{}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.binarySteps(Types.Production{lhs, [Types.Nonterminal{b2}]} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [Types.Nonterminal{b2}], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Con{Types.Terminal{t}, more}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.binarySteps(Types.Production{lhs, Types.Nonterminal{b2} <> Types.Terminal{t} <> more} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Nonterminal{b2} <> Types.Terminal{t} <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Nonterminal{b2}, Con{Types.Nonterminal{c2}, Con{x, more}}}:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{o, i, k, j}, Grammar.binarySteps(Types.Production{lhs, Types.Nonterminal{b2} <> Types.Nonterminal{c2} <> x <> more} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), Types.Nonterminal{b2} <> Types.Nonterminal{c2} <> x <> more, [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))


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
      bsr_member_keep(Bool.and(Grammar.natMember(b, lefts), Grammar.natMember(c, rights)), Types.Bsr{o, i, k, j}, Grammar.binarySteps(others, lefts, rights, i, k, j, 1n+o), element, e)
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
  for rhsOk: {GrammarLaws.rhsOf(rest, index) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
  for +inLefts: {Grammar.natMember(b, lefts) == True{} : Bool}
  for +inRights: {Grammar.natMember(c, rights) == True{} : Bool}
  {GrammarLaws.bsrMember(Types.Bsr{Nat.add(o, index), i, k, j}, Grammar.binarySteps(rest, lefts, rights, i, k, j, o)) == True{} : Bool}

def binary_steps_member(rest, lefts, rights, i, k, j, o, index, b, c, rhsOk, inLefts, inRights):
  match rest index:
    case Nil{} _:
      Empty.absurd({GrammarLaws.bsrMember(Types.Bsr{Nat.add(o, index), i, k, j}, []) == True{} : Bool}, Lemma.false_is_not_true(Equal.cong(+List<Types.Symbol>, Bool, l => isNonterminalPair(l), [], [Types.Nonterminal{b}, Types.Nonterminal{c}], rhsOk)))
    case Con{Types.Production{+lhs, +rhs}, +others} 0n:
      %Equal.sym(Nat, Nat.add(o, 0n), o, Lemma.add_zero_right(o)) : {GrammarLaws.bsrMember(Types.Bsr{_, i, k, j}, Grammar.binarySteps(Types.Production{lhs, rhs} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}
      binary_head_member(lhs, rhs, others, lefts, rights, i, k, j, o, b, c, rhsOk, inLefts, inRights)
    case Con{Types.Production{+lhs, +rhs}, +others} 1n+(+index2):
      %Equal.sym(Nat, Nat.add(o, 1n+index2), 1n+Nat.add(o, index2), Lemma.add_succ_right(o, index2)) : {GrammarLaws.bsrMember(Types.Bsr{_, i, k, j}, Grammar.binarySteps(Types.Production{lhs, rhs} <> others, lefts, rights, i, k, j, o)) == True{} : Bool}
      binary_steps_skip(lhs, rhs, others, lefts, rights, i, k, j, o, Types.Bsr{Nat.add(1n+o, index2), i, k, j}, binary_steps_member(others, lefts, rights, i, k, j, 1n+o, index2, b, c, rhsOk, inLefts, inRights))


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


# ---- Completeness: every node of a parse tree has its step in the set ----

def InSet(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +tree: Types.Tree, +s: Nat) -> Type:
  {GrammarLaws.embedded(tree, Grammar.bsrSet(grammar, inputTokens), s) == True{} : Bool}


law token_member:
  for +grammar: +List<Types.Production>
  for +inputTokens: +List<Nat>
  for +s: Nat
  for +p: Nat
  for +kind: Nat
  for tokenEq: {List.get(&2, Nat, inputTokens, s) == Some{kind} : Maybe<&2, Nat>}
  for rhsOk: {GrammarLaws.rhsOf(grammar, p) == [Types.Terminal{kind}] : +List<Types.Symbol>}
  {GrammarLaws.bsrMember(Types.Bsr{p, s, s, 1n+s}, Grammar.tokenSteps(grammar, List.get(&2, Nat, inputTokens, s), s)) == True{} : Bool}

def token_member(grammar, inputTokens, s, p, kind, tokenEq, rhsOk):
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, inputTokens, s), Some{kind}, tokenEq) : {GrammarLaws.bsrMember(Types.Bsr{p, s, s, 1n+s}, Grammar.tokenSteps(grammar, _, s)) == True{} : Bool}
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
      all_member(grammar, inputTokens, table, count, 0n, Types.Bsr{p, s, s, 1n+s}, count, Lemma.lt_pos(s, count, lt), row_member(grammar, inputTokens, table, 1n, s, Types.Bsr{p, s, s, 1n+s}, count, lt, inSpan))


# The induction hypothesis for a child tree, passed as a function.
def ChildInSet(+grammar: +List<Types.Production>, +inputTokens: +List<Nat>, +child: Types.Tree) -> Type:
  @b: Nat -> @s: Nat -> @l: Nat -> {GrammarLaws.fits([child], grammar, [Types.Nonterminal{b}]) == True{} : Bool} -> {Lemma.slice(inputTokens, s, l) == GrammarLaws.leaves([child]) : +List<Nat>} -> {List.length(&2, Nat, GrammarLaws.leaves([child])) == l : Nat} -> {Nat.is_le(l, List.length(&2, Nat, inputTokens)) == True{} : Bool} -> InSet(grammar, inputTokens, child, s)


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
  for lhsOk: {GrammarLaws.lhsIs(grammar, p, a) == True{} : Bool}
  for rhsOk: {GrammarLaws.rhsOf(grammar, p) == [Types.Nonterminal{b}, Types.Nonterminal{c}] : +List<Types.Symbol>}
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
      +element = {Types.Bsr{p, s, Nat.add(s, 1n+p1), Nat.add(s, Nat.add(1n+p1, 1n+q2))} : Types.Bsr}
      hit = binary_steps_member(grammar, Grammar.lookup(table, s, 1n+p1), Grammar.lookup(table, Nat.add(s, 1n+p1), 1n+q2), s, Nat.add(s, 1n+p1), Nat.add(s, Nat.add(1n+p1, 1n+q2)), 0n, p, b, c, rhsOk, inLefts, inRights)
      sum = Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p1, 1n+q2), Nat.add(m, 1n), Equal.trans(Nat, Nat.add(p1, 1n+q2), 1n+m, Nat.add(m, 1n), Lemma.add_succ_right(p1, q2), Equal.sym(Nat, Nat.add(m, 1n), 1n+m, Lemma.add_one_right(m))))
      inSplit = split_steps_member(grammar, table, s, element, p1, 1n+q2, 1n+m, 1n, Lemma.le_add_right(p1, q2), sum, hit)
      +lt = Lemma.slice_start_lt(inputTokens, s, Nat.add(1n+p1, 1n+q2), h1, List.append(&2, Nat, r1, w2), atSum)
      leTwo = Equal.trans(Bool, Nat.is_le(1n+1n+m, count), Nat.is_le(l, count), True{}, Equal.cong(Nat, Bool, n => Nat.is_le(n, count), 1n+1n+m, l, Equal.sym(Nat, l, 1n+1n+m, lTwo)), le)
      inAll = all_member(grammar, inputTokens, table, count, 1n+m, element, count, leTwo, row_member(grammar, inputTokens, table, 1n+1n+m, s, element, count, lt, inSplit))
      +set = Grammar.bsrSet(grammar, inputTokens)
      %Equal.sym(+List<Nat>, GrammarLaws.leaves([first]), w1, e1) : {Bool.and(GrammarLaws.bsrMember(Types.Bsr{p, s, Nat.add(s, List.length(&2, Nat, _)), Nat.add(Nat.add(s, List.length(&2, Nat, _)), List.length(&2, Nat, GrammarLaws.leaves([second])))}, set), Bool.and(GrammarLaws.embedded(first, set, s), GrammarLaws.embedded(second, set, Nat.add(s, List.length(&2, Nat, _))))) == True{} : Bool}
      %Equal.sym(+List<Nat>, GrammarLaws.leaves([second]), w2, e2) : {Bool.and(GrammarLaws.bsrMember(Types.Bsr{p, s, Nat.add(s, 1n+p1), Nat.add(Nat.add(s, 1n+p1), List.length(&2, Nat, _))}, set), Bool.and(GrammarLaws.embedded(first, set, s), GrammarLaws.embedded(second, set, Nat.add(s, 1n+p1)))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(Nat.add(s, 1n+p1), 1n+q2), Nat.add(s, Nat.add(1n+p1, 1n+q2)), Lemma.add_assoc(s, 1n+p1, 1n+q2)) : {Bool.and(GrammarLaws.bsrMember(Types.Bsr{p, s, Nat.add(s, 1n+p1), _}, set), Bool.and(GrammarLaws.embedded(first, set, s), GrammarLaws.embedded(second, set, Nat.add(s, 1n+p1)))) == True{} : Bool}
      Lemma.and_true_intro(
        GrammarLaws.bsrMember(element, set),
        Bool.and(GrammarLaws.embedded(first, set, s), GrammarLaws.embedded(second, set, Nat.add(s, 1n+p1))),
        inAll,
        Lemma.and_true_intro(GrammarLaws.embedded(first, set, s), GrammarLaws.embedded(second, set, Nat.add(s, 1n+p1)), inFirst, inSecond))


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

def GrammarLaws.bsr_every_parse_tree(grammar, start, inputTokens, tree, binary, fitting, spelled):
  +count = List.length(&2, Nat, inputTokens)
  +both = spelled
  tree_in_set(
    tree, grammar, inputTokens, binary, start, 0n, count, fitting,
    Equal.trans(+List<Nat>, Lemma.takeN(count, inputTokens), inputTokens, GrammarLaws.leaves([tree]), Lemma.take_length(inputTokens), Equal.sym(+List<Nat>, GrammarLaws.leaves([tree]), inputTokens, both)),
    Equal.cong(+List<Nat>, Nat, x => List.length(&2, Nat, x), GrammarLaws.leaves([tree]), inputTokens, both),
    Lemma.le_refl(count))
