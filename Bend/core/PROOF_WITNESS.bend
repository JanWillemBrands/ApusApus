import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./WITNESS.bend as W
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as PP
import ./PROOF_COUNT.bend as C
import ./RUN.bend as Run
import ./PROOF_NEEDS.bend as N

# THE WITNESS SEARCH FINDS WHAT IS THERE (WITNESS.bend). If the facts are closed under the
# rules of the kept steps, and a parse tree made of kept steps contains the target, then the
# root has a flagged forest. The proof walks the tree left to right: every prefix of every
# node has a fact, with the flag the rules give it (`cflag`).

# ======== FLAGS AND OPTIONS ========

def bool_eq_refl(b: Bool) -> {W.boolEq(b, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law bool_eq_sound:
  for a: Bool
  for b: Bool
  for +e: {W.boolEq(a, b) == True{} : Bool}
  {a == b : Bool}

def bool_eq_sound(a, b, e):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Lemma.false_is_not_true(e))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(e))
    case False{} False{}:
      {==}

# Some option of the list has this flag.
def optHas(+f: Bool, os: +List<W.Opt>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{W.Opt{+fl, fo}, rest}:
      Bool.or(W.boolEq(f, fl), optHas(f, rest))

def isSingle(fo: +List<Core.Tree>) -> Bool:
  match fo:
    case Con{t, Nil{}}:
      True{}
    case _:
      False{}

# Some option of the list has this flag and one tree.
def itemHas(+f: Bool, os: +List<W.Opt>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{W.Opt{+fl, +fo}, rest}:
      Bool.or(Bool.and(W.boolEq(f, fl), isSingle(fo)), itemHas(f, rest))

def opt_pick(+f: Bool, +fl: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Opt>, +ys: +List<W.Opt>,
  cases: Either<{W.boolEq(f, fl) == True{} : Bool}, {optHas(f, rest) == True{} : Bool}>,
  later: {optHas(f, rest) == True{} : Bool} -> {optHas(f, List.append(&2, W.Opt, rest, ys)) == True{} : Bool})
  -> {optHas(f, W.Opt{fl, fo} <> List.append(&2, W.Opt, rest, ys)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(W.boolEq(f, fl), optHas(f, List.append(&2, W.Opt, rest, ys)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(W.boolEq(f, fl), optHas(f, List.append(&2, W.Opt, rest, ys)), later(m))

law opt_app_left:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +f: Bool
  for +h: {optHas(f, xs) == True{} : Bool}
  {optHas(f, List.append(&2, W.Opt, xs, ys)) == True{} : Bool}

def opt_app_left(xs, ys, f, h):
  match xs:
    case Nil{}:
      Empty.absurd({optHas(f, ys) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+fl, +fo}, +rest}:
      opt_pick(f, fl, fo, rest, ys, Lemma.or_true_cases(W.boolEq(f, fl), optHas(f, rest), h), m => opt_app_left(rest, ys, f, m))

law opt_app_right:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +f: Bool
  for +h: {optHas(f, ys) == True{} : Bool}
  {optHas(f, List.append(&2, W.Opt, xs, ys)) == True{} : Bool}

def opt_app_right(xs, ys, f, h):
  match xs:
    case Nil{}:
      h
    case Con{W.Opt{+fl, +fo}, +rest}:
      Lemma.or_true_right_intro(W.boolEq(f, fl), optHas(f, List.append(&2, W.Opt, rest, ys)), opt_app_right(rest, ys, f, h))

def item_pick(+f: Bool, +fl: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Opt>, +ys: +List<W.Opt>,
  cases: Either<{Bool.and(W.boolEq(f, fl), isSingle(fo)) == True{} : Bool}, {itemHas(f, rest) == True{} : Bool}>,
  later: {itemHas(f, rest) == True{} : Bool} -> {itemHas(f, List.append(&2, W.Opt, rest, ys)) == True{} : Bool})
  -> {itemHas(f, W.Opt{fl, fo} <> List.append(&2, W.Opt, rest, ys)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Bool.and(W.boolEq(f, fl), isSingle(fo)), itemHas(f, List.append(&2, W.Opt, rest, ys)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Bool.and(W.boolEq(f, fl), isSingle(fo)), itemHas(f, List.append(&2, W.Opt, rest, ys)), later(m))

law item_app_left:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +f: Bool
  for +h: {itemHas(f, xs) == True{} : Bool}
  {itemHas(f, List.append(&2, W.Opt, xs, ys)) == True{} : Bool}

def item_app_left(xs, ys, f, h):
  match xs:
    case Nil{}:
      Empty.absurd({itemHas(f, ys) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+fl, +fo}, +rest}:
      item_pick(f, fl, fo, rest, ys, Lemma.or_true_cases(Bool.and(W.boolEq(f, fl), isSingle(fo)), itemHas(f, rest), h), m => item_app_left(rest, ys, f, m))

law item_app_right:
  for xs: +List<W.Opt>
  for +ys: +List<W.Opt>
  for +f: Bool
  for +h: {itemHas(f, ys) == True{} : Bool}
  {itemHas(f, List.append(&2, W.Opt, xs, ys)) == True{} : Bool}

def item_app_right(xs, ys, f, h):
  match xs:
    case Nil{}:
      h
    case Con{W.Opt{+fl, +fo}, +rest}:
      Lemma.or_true_right_intro(Bool.and(W.boolEq(f, fl), isSingle(fo)), itemHas(f, List.append(&2, W.Opt, rest, ys)), item_app_right(rest, ys, f, h))

# ---- What the rules do to a flag ----

def mark_head(+f: Bool, +fl: Bool, +here: Bool, +e: {f == fl : Bool}) -> {W.boolEq(Bool.or(f, here), Bool.or(fl, here)) == True{} : Bool}:
  %e : {W.boolEq(Bool.or(f, here), Bool.or(_, here)) == True{} : Bool}
  bool_eq_refl(Bool.or(f, here))

def mark_pick(+f: Bool, +fl: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Opt>, +here: Bool,
  cases: Either<{W.boolEq(f, fl) == True{} : Bool}, {optHas(f, rest) == True{} : Bool}>,
  later: {optHas(f, rest) == True{} : Bool} -> {optHas(Bool.or(f, here), W.markIf(here, rest)) == True{} : Bool})
  -> {optHas(Bool.or(f, here), W.markIf(here, W.Opt{fl, fo} <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(W.boolEq(Bool.or(f, here), Bool.or(fl, here)), optHas(Bool.or(f, here), W.markIf(here, rest)), mark_head(f, fl, here, bool_eq_sound(f, fl, e)))
    case Inr{m}:
      Lemma.or_true_right_intro(W.boolEq(Bool.or(f, here), Bool.or(fl, here)), optHas(Bool.or(f, here), W.markIf(here, rest)), later(m))

law opt_mark:
  for os: +List<W.Opt>
  for +f: Bool
  for +here: Bool
  for +h: {optHas(f, os) == True{} : Bool}
  {optHas(Bool.or(f, here), W.markIf(here, os)) == True{} : Bool}

def opt_mark(os, f, here, h):
  match os:
    case Nil{}:
      Empty.absurd({optHas(Bool.or(f, here), []) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+fl, +fo}, +rest}:
      mark_pick(f, fl, fo, rest, here, Lemma.or_true_cases(W.boolEq(f, fl), optHas(f, rest), h), m => opt_mark(rest, f, here, m))

def with_pick(+f: Bool, +fl: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Opt>, +tree: Core.Tree, +f2: Bool,
  cases: Either<{W.boolEq(f, fl) == True{} : Bool}, {optHas(f, rest) == True{} : Bool}>,
  later: {optHas(f, rest) == True{} : Bool} -> {optHas(Bool.or(f, f2), W.withTree(tree, f2, rest)) == True{} : Bool})
  -> {optHas(Bool.or(f, f2), W.withTree(tree, f2, W.Opt{fl, fo} <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(W.boolEq(Bool.or(f, f2), Bool.or(fl, f2)), optHas(Bool.or(f, f2), W.withTree(tree, f2, rest)), mark_head(f, fl, f2, bool_eq_sound(f, fl, e)))
    case Inr{m}:
      Lemma.or_true_right_intro(W.boolEq(Bool.or(f, f2), Bool.or(fl, f2)), optHas(Bool.or(f, f2), W.withTree(tree, f2, rest)), later(m))

law opt_with:
  for os: +List<W.Opt>
  for +tree: Core.Tree
  for +f2: Bool
  for +f: Bool
  for +h: {optHas(f, os) == True{} : Bool}
  {optHas(Bool.or(f, f2), W.withTree(tree, f2, os)) == True{} : Bool}

def opt_with(os, tree, f2, f, h):
  match os:
    case Nil{}:
      Empty.absurd({optHas(Bool.or(f, f2), []) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+fl, +fo}, +rest}:
      with_pick(f, fl, fo, rest, tree, f2, Lemma.or_true_cases(W.boolEq(f, fl), optHas(f, rest), h), m => opt_with(rest, tree, f2, f, m))

def flag_to(+f1: Bool, +f2: Bool, +g: Bool, +os: +List<W.Opt>, +e: {f2 == g : Bool},
  +h: {optHas(Bool.or(f1, g), os) == True{} : Bool}) -> {optHas(Bool.or(f1, f2), os) == True{} : Bool}:
  %Equal.sym(Bool, f2, g, e) : {optHas(Bool.or(f1, _), os) == True{} : Bool}
  h

def join_head(t: +List<Core.Tree>, +f1: Bool, +f2: Bool, +g: Bool, +prefixes: +List<W.Opt>,
  +hp: {optHas(f1, prefixes) == True{} : Bool},
  +h: {Bool.and(W.boolEq(f2, g), isSingle(t)) == True{} : Bool})
  -> {optHas(Bool.or(f1, f2), W.withTreeList(t, g, prefixes)) == True{} : Bool}:
  match t:
    case Nil{}:
      Empty.absurd({optHas(Bool.or(f1, f2), []) == True{} : Bool}, Lemma.false_is_not_true(Lemma.and_true_right_side(W.boolEq(f2, g), False{}, h)))
    case Con{+tree, Nil{}}:
      flag_to(f1, f2, g, W.withTree(tree, g, prefixes), bool_eq_sound(f2, g, Lemma.and_true_left(W.boolEq(f2, g), True{}, h)), opt_with(prefixes, tree, g, f1, hp))
    case Con{+tree, Con{+t2, +more}}:
      Empty.absurd({optHas(Bool.or(f1, f2), []) == True{} : Bool}, Lemma.false_is_not_true(Lemma.and_true_right_side(W.boolEq(f2, g), False{}, h)))

def join_pick(+f1: Bool, +f2: Bool, +g: Bool, +t: +List<Core.Tree>, +rest: +List<W.Opt>, +prefixes: +List<W.Opt>,
  +hp: {optHas(f1, prefixes) == True{} : Bool},
  cases: Either<{Bool.and(W.boolEq(f2, g), isSingle(t)) == True{} : Bool}, {itemHas(f2, rest) == True{} : Bool}>,
  later: {itemHas(f2, rest) == True{} : Bool} -> {optHas(Bool.or(f1, f2), W.joinAll(prefixes, rest)) == True{} : Bool})
  -> {optHas(Bool.or(f1, f2), W.joinAll(prefixes, W.Opt{g, t} <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      opt_app_left(W.withTreeList(t, g, prefixes), W.joinAll(prefixes, rest), Bool.or(f1, f2), join_head(t, f1, f2, g, prefixes, hp, e))
    case Inr{m}:
      opt_app_right(W.withTreeList(t, g, prefixes), W.joinAll(prefixes, rest), Bool.or(f1, f2), later(m))

# A prefix with flag f1 and an item with flag f2 give a forest with flag f1 or f2.
law join_has:
  for +prefixes: +List<W.Opt>
  for items: +List<W.Opt>
  for +f1: Bool
  for +f2: Bool
  for +hp: {optHas(f1, prefixes) == True{} : Bool}
  for +hi: {itemHas(f2, items) == True{} : Bool}
  {optHas(Bool.or(f1, f2), W.joinAll(prefixes, items)) == True{} : Bool}

def join_has(prefixes, items, f1, f2, hp, hi):
  match items:
    case Nil{}:
      Empty.absurd({optHas(Bool.or(f1, f2), []) == True{} : Bool}, Lemma.false_is_not_true(hi))
    case Con{W.Opt{+g, +t}, +rest}:
      join_pick(f1, f2, g, t, rest, prefixes, hp, Lemma.or_true_cases(Bool.and(W.boolEq(f2, g), isSingle(t)), itemHas(f2, rest), hi),
        m => join_has(prefixes, rest, f1, f2, hp, m))

# ---- Facts ----

def found_head(b: Bool, +f: Bool, +fl: Bool, +fo: +List<Core.Tree>, +more: +List<W.Opt>,
  +h: {Bool.and(b, W.boolEq(f, fl)) == True{} : Bool}) -> {optHas(f, W.optIf(b, W.Opt{fl, fo}, more)) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.or_true_left_intro(W.boolEq(f, fl), optHas(f, more), h)
    case False{}:
      Empty.absurd({optHas(f, more) == True{} : Bool}, Lemma.false_is_not_true(h))

def found_tail(b: Bool, +f: Bool, +fl: Bool, +fo: +List<Core.Tree>, +more: +List<W.Opt>,
  +h: {optHas(f, more) == True{} : Bool}) -> {optHas(f, W.optIf(b, W.Opt{fl, fo}, more)) == True{} : Bool}:
  match b:
    case True{}:
      Lemma.or_true_right_intro(W.boolEq(f, fl), optHas(f, more), h)
    case False{}:
      h

def found_pick(+b: Bool, +f: Bool, +fl: Bool, +fo: +List<Core.Tree>, +more: +List<W.Opt>, +R: Bool, later2: {R == True{} : Bool} -> {optHas(f, W.optIf(b, W.Opt{fl, fo}, more)) == True{} : Bool},
  cases: Either<{Bool.and(b, W.boolEq(f, fl)) == True{} : Bool}, {R == True{} : Bool}>)
  -> {optHas(f, W.optIf(b, W.Opt{fl, fo}, more)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      found_head(b, f, fl, fo, more, e)
    case Inr{m}:
      later2(m)

law found_has:
  for facts: +List<W.Fact>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +f: Bool
  for +h: {W.hasFact(q, ks, d, e, f, facts) == True{} : Bool}
  {optHas(f, W.foundAt(q, ks, d, e, facts)) == True{} : Bool}

def found_has(facts, q, ks, d, e, f, h):
  match facts:
    case Nil{}:
      Empty.absurd({optHas(f, []) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Fact{+q2, +ks2, +d2, +e2, +fl, +fo}, +rest}:
      +b = W.sameKey(q, ks, d, e, W.Fact{q2, ks2, d2, e2, fl, fo})
      found_pick(b, f, fl, fo, W.foundAt(q, ks, d, e, rest), W.hasFact(q, ks, d, e, f, rest), m => found_tail(b, f, fl, fo, W.foundAt(q, ks, d, e, rest), found_has(rest, q, ks, d, e, f, m)),
        Lemma.or_true_cases(Bool.and(b, W.boolEq(f, fl)), W.hasFact(q, ks, d, e, f, rest), h))

# ======== CLOSED FACTS ========

# Every fact the list makes is already there (by key and flag).
def factsIn(fs: +List<W.Fact>, +facts: +List<W.Fact>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{W.Fact{+q, +ks, +d, +e, +fl, fo}, rest}:
      Bool.and(W.hasFact(q, ks, d, e, fl, facts), factsIn(rest, facts))

# The facts are closed under the rules of the steps.
def closedW(ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+e, rest}:
      Bool.and(factsIn(W.stepFacts(grammar, input, target, F, e), F), closedW(rest, grammar, input, target, F))

def facts_head(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fl: Bool, +F: +List<W.Fact>, +eq: {f == fl : Bool},
  +h: {W.hasFact(q, ks, d, e, fl, F) == True{} : Bool}) -> {W.hasFact(q, ks, d, e, f, F) == True{} : Bool}:
  %Equal.sym(Bool, f, fl, eq) : {W.hasFact(q, ks, d, e, _, F) == True{} : Bool}
  h

def facts_pick(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fl: Bool, +F: +List<W.Fact>, +R: Bool,
  +hf: {W.hasFact(q, ks, d, e, fl, F) == True{} : Bool},
  cases: Either<{W.boolEq(f, fl) == True{} : Bool}, {R == True{} : Bool}>,
  later: {R == True{} : Bool} -> {W.hasFact(q, ks, d, e, f, F) == True{} : Bool}) -> {W.hasFact(q, ks, d, e, f, F) == True{} : Bool}:
  match cases:
    case Inl{x}:
      facts_head(q, ks, d, e, f, fl, F, bool_eq_sound(f, fl, x), hf)
    case Inr{m}:
      later(m)

# An option whose fact is in a closed set.
law facts_of_has:
  for os: +List<W.Opt>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +f: Bool
  for +F: +List<W.Fact>
  for +h: {optHas(f, os) == True{} : Bool}
  for +c: {factsIn(W.factsOf(q, ks, d, e, os), F) == True{} : Bool}
  {W.hasFact(q, ks, d, e, f, F) == True{} : Bool}

def facts_of_has(os, q, ks, d, e, f, F, h, c):
  match os:
    case Nil{}:
      Empty.absurd({W.hasFact(q, ks, d, e, f, F) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+fl, +fo}, +rest}:
      +hf = {W.hasFact(q, ks, d, e, fl, F) : Bool}
      facts_pick(q, ks, d, e, f, fl, F, optHas(f, rest), Lemma.and_true_left(hf, factsIn(W.factsOf(q, ks, d, e, rest), F), c),
        Lemma.or_true_cases(W.boolEq(f, fl), optHas(f, rest), h),
        m => facts_of_has(rest, q, ks, d, e, f, F, m, Lemma.and_true_right_side(hf, factsIn(W.factsOf(q, ks, d, e, rest), F), c)))

def closed_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>,
  +hy: {factsIn(W.stepFacts(grammar, input, target, F, y), F) == True{} : Bool},
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {factsIn(W.stepFacts(grammar, input, target, F, x), F) == True{} : Bool})
  -> {factsIn(W.stepFacts(grammar, input, target, F, x), F) == True{} : Bool}:
  match cases:
    case Inl{e}:
      %Equal.sym(Core.Bsr, x, y, G.bsr_eq_sound(x, y, e)) : {factsIn(W.stepFacts(grammar, input, target, F, _), F) == True{} : Bool}
      hy
    case Inr{m}:
      later(m)

law closed_at:
  for ps: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +x: Core.Bsr
  for +m: {Core.member(x, ps) == True{} : Bool}
  for +c: {closedW(ps, grammar, input, target, F) == True{} : Bool}
  {factsIn(W.stepFacts(grammar, input, target, F, x), F) == True{} : Bool}

def closed_at(ps, grammar, input, target, F, x, m, c):
  match ps:
    case Nil{}:
      Empty.absurd({factsIn(W.stepFacts(grammar, input, target, F, x), F) == True{} : Bool}, Lemma.false_is_not_true(m))
    case Con{+y, +rest}:
      +hy = {factsIn(W.stepFacts(grammar, input, target, F, y), F) : Bool}
      closed_pick(x, y, rest, grammar, input, target, F, Lemma.and_true_left(hy, closedW(rest, grammar, input, target, F), c),
        Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), m),
        m2 => closed_at(rest, grammar, input, target, F, x, m2, Lemma.and_true_right_side(hy, closedW(rest, grammar, input, target, F), c)))

# ======== ONE STEP OF THE TREE ========

# A kept step after a prefix with flag fd and an item with flag ft: the segment after it has
# a fact with the flag the rules give.
def step_fact(+grammar: +List<Core.Production>, +input: +List<Nat>, +ps: +List<Core.Bsr>, +target: Core.Bsr, +F: +List<W.Fact>, +cl: {closedW(ps, grammar, input, target, F) == True{} : Bool}, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +j: Nat, +fd: Bool, +ft: Bool,
  +hp: {optHas(fd, W.optsAt(grammar, target, q, ks, d, k, F)) == True{} : Bool},
  +hi: {itemHas(ft, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, F)) == True{} : Bool},
  +m: {Core.member(Core.Bsr{q, 1n+d, ks, k, j}, ps) == True{} : Bool})
  -> {optHas(Bool.or(Bool.or(fd, ft), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target)), W.optsAt(grammar, target, q, ks, 1n+d, j, F)) == True{} : Bool}:
  +here = Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target)
  +joined = W.joinAll(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, F))
  +flag = {Bool.or(Bool.or(fd, ft), here) : Bool}
  found_has(F, q, ks, 1n+d, j, flag,
    facts_of_has(W.markIf(here, joined), q, ks, 1n+d, j, flag, F, opt_mark(joined, Bool.or(fd, ft), here, join_has(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, F), fd, ft, hp, hi)),
      closed_at(ps, grammar, input, target, F, Core.Bsr{q, 1n+d, ks, k, j}, m, cl)))

def tok_to(+input: +List<Nat>, +k: Nat, +a: Nat, +t: Nat, +e: {a == t : Nat},
  +h: {Core.tokIs(Core.tokAt(input, k), a) == True{} : Bool}) -> {Core.tokIs(Core.tokAt(input, k), t) == True{} : Bool}:
  %e : {Core.tokIs(Core.tokAt(input, k), _) == True{} : Bool}
  h

def leaf_pick(b: Bool, +t: Nat, +eb: {b == True{} : Bool}) -> {itemHas(False{}, W.leafIf(b, t)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({itemHas(False{}, []) == True{} : Bool}, Lemma.false_is_not_true(eb))

# A leaf reading its token is an item option, unflagged.
def leaf_item(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +k: Nat, +a: Nat, +t: Nat,
  +eq: {Nat.is_eq(a, t) == True{} : Bool}, +tok: {Core.tokIs(Core.tokAt(input, k), a) == True{} : Bool})
  -> {itemHas(False{}, W.itemOpts(Some{Core.Terminal{t}}, grammar, input, target, k, 1n+k, F)) == True{} : Bool}:
  leaf_pick(Bool.and(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(1n+k, 1n+k)), t,
    Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), t), Nat.is_eq(1n+k, 1n+k), tok_to(input, k, a, t, Lemma.nat_eq_sound(a, t, eq), tok), Lemma.nat_eq_refl(1n+k)))

def node_pick(+q2: Nat, +fl: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Opt>, +f: Bool,
  cases: Either<{W.boolEq(f, fl) == True{} : Bool}, {optHas(f, rest) == True{} : Bool}>,
  later: {optHas(f, rest) == True{} : Bool} -> {itemHas(f, W.nodeOpts(q2, rest)) == True{} : Bool})
  -> {itemHas(f, W.nodeOpts(q2, W.Opt{fl, fo} <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Bool.and(W.boolEq(f, fl), True{}), itemHas(f, W.nodeOpts(q2, rest)), Lemma.and_true_intro(W.boolEq(f, fl), True{}, e, {==}))
    case Inr{m}:
      Lemma.or_true_right_intro(Bool.and(W.boolEq(f, fl), True{}), itemHas(f, W.nodeOpts(q2, rest)), later(m))

def node_has(+q2: Nat, os: +List<W.Opt>, +f: Bool, +h: {optHas(f, os) == True{} : Bool}) -> {itemHas(f, W.nodeOpts(q2, os)) == True{} : Bool}:
  match os:
    case Nil{}:
      Empty.absurd({itemHas(f, []) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+fl, +fo}, +rest}:
      node_pick(q2, fl, fo, rest, f, Lemma.or_true_cases(W.boolEq(f, fl), optHas(f, rest), h), m => node_has(q2, rest, f, m))

def need_pick(b: Bool, +os: +List<W.Opt>, +f: Bool, +eb: {b == True{} : Bool}, +h: {itemHas(f, os) == True{} : Bool})
  -> {itemHas(f, W.needIf(b, os)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({itemHas(f, []) == True{} : Bool}, Lemma.false_is_not_true(eb))

def prod_here(b: Bool, +grammar: +List<Core.Production>, +target: Core.Bsr, +base: Nat, +len: Nat, +k: Nat, +j: Nat, +F: +List<W.Fact>, +f: Bool,
  +eb: {b == True{} : Bool}, +h: {itemHas(f, W.nodeOpts(base, W.optsAt(grammar, target, base, k, len, j, F))) == True{} : Bool})
  -> {itemHas(f, W.prodPick(b, grammar, target, base, len, k, j, F)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({itemHas(f, []) == True{} : Bool}, Lemma.false_is_not_true(eb))

def base_zero(+grammar: +List<Core.Production>, +target: Core.Bsr, +base: Nat, +len: Nat, +k: Nat, +j: Nat, +F: +List<W.Fact>, +f: Bool,
  +h: {itemHas(f, W.nodeOpts(Nat.add(base, 0n), W.optsAt(grammar, target, Nat.add(base, 0n), k, len, j, F))) == True{} : Bool})
  -> {itemHas(f, W.nodeOpts(base, W.optsAt(grammar, target, base, k, len, j, F))) == True{} : Bool}:
  %Lemma.add_zero_right(base) : {itemHas(f, W.nodeOpts(_, W.optsAt(grammar, target, _, k, len, j, F))) == True{} : Bool}
  h

def base_succ(+grammar: +List<Core.Production>, +target: Core.Bsr, +base: Nat, +n: Nat, +len: Nat, +k: Nat, +j: Nat, +F: +List<W.Fact>, +f: Bool,
  +h: {itemHas(f, W.nodeOpts(Nat.add(base, 1n+n), W.optsAt(grammar, target, Nat.add(base, 1n+n), k, len, j, F))) == True{} : Bool})
  -> {itemHas(f, W.nodeOpts(Nat.add(1n+base, n), W.optsAt(grammar, target, Nat.add(1n+base, n), k, len, j, F))) == True{} : Bool}:
  %Lemma.add_succ_right(base, n) : {itemHas(f, W.nodeOpts(_, W.optsAt(grammar, target, _, k, len, j, F))) == True{} : Bool}
  h

# The production at q of g (the grammar from base on) gives its node options.
law prod_has:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +target: Core.Bsr
  for +k: Nat
  for +j: Nat
  for +F: +List<W.Fact>
  for +f: Bool
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  for +hi: {itemHas(f, W.nodeOpts(Nat.add(base, q), W.optsAt(grammar, target, Nat.add(base, q), k, List.length(&2, Core.Sym, Core.rhsOf(g, q)), j, F))) == True{} : Bool}
  {itemHas(f, W.prodOpts(g, grammar, target, base, x, k, j, F)) == True{} : Bool}

def prod_has(g, q, x, base, grammar, target, k, j, F, f, h, hi):
  match g q:
    case Nil{} +q0:
      Empty.absurd({itemHas(f, []) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +len = List.length(&2, Core.Sym, rhs)
      item_app_left(W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F), f,
        prod_here(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F, f, h, base_zero(grammar, target, base, len, k, j, F, f, hi)))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      +len = List.length(&2, Core.Sym, rhs)
      item_app_right(W.prodPick(Nat.is_eq(lhs, x), grammar, target, base, len, k, j, F), W.prodOpts(rest, grammar, target, 1n+base, x, k, j, F), f,
        prod_has(rest, n, x, 1n+base, grammar, target, k, j, F, f, h, base_succ(grammar, target, base, n, List.length(&2, Core.Sym, Core.rhsOf(rest, n)), k, j, F, f, hi)))

# A node of x reading k .. j is an item option, with its own forest's flag.
def node_item(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +q2: Nat, +ch: +List<Core.Tree>, +k: Nat, +x: Nat, +need: Core.Need, +f: Bool,
  +lhs: {Core.lhsIs(grammar, q2, x) == True{} : Bool},
  +nk: {Core.needOk(need, Core.width(Core.Node{q2, ch})) == True{} : Bool},
  +hc: {optHas(f, W.optsAt(grammar, target, q2, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, q2)), Nat.add(k, Core.width(Core.Node{q2, ch})), F)) == True{} : Bool})
  -> {itemHas(f, W.itemOpts(Some{Core.Nonterminal{x, need}}, grammar, input, target, k, Nat.add(k, Core.width(Core.Node{q2, ch})), F)) == True{} : Bool}:
  +j = Nat.add(k, Core.width(Core.Node{q2, ch}))
  need_pick(Gll.needHolds(need, k, j), W.prodOpts(grammar, grammar, target, 0n, x, k, j, F), f, G.need_holds(need, Core.width(Core.Node{q2, ch}), k, nk),
    prod_has(grammar, q2, x, 0n, grammar, target, k, j, F, f, lhs,
      node_has(q2, W.optsAt(grammar, target, q2, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, q2)), j, F), f, hc)))

def item_at(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +d: Nat, +y: Core.Sym, +rest: +List<Core.Sym>, +k: Nat, +j: Nat, +f: Bool,
  +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == y <> rest : +List<Core.Sym>},
  +h: {itemHas(f, W.itemOpts(Some{y}, grammar, input, target, k, j, F)) == True{} : Bool}) -> {itemHas(f, W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, F)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Core.Sym>, Gll.nthSym(Core.rhsOf(grammar, q), d), Some{y}, G.nth_drop(Core.rhsOf(grammar, q), d, y, rest, ie)) : {itemHas(f, W.itemOpts(_, grammar, input, target, k, j, F)) == True{} : Bool}
  h

# ======== THE WALK ========

# The flag of the empty prefix of production q at ks.
def startFlag(+grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat) -> Bool:
  Bool.and(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q)), Core.bsrEq(Core.Bsr{q, 0n, ks, ks, ks}, target))

# The flag the rules give the forest f read from k, after a prefix with flag fd, in a node of
# q started at ks, from dot d on.
def cflag(f: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, fd: Bool) -> Bool:
  match f:
    case Nil{}:
      fd
    case Con{Core.Leaf{a}, ts}:
      cflag(ts, grammar, target, q, ks, 1n+d, 1n+k, Bool.or(Bool.or(fd, False{}), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, 1n+k}, target)))
    case Con{Core.Node{+q2, +ch}, ts}:
      +far = Nat.add(k, Core.width(Core.Node{q2, ch}))
      cflag(ts, grammar, target, q, ks, 1n+d, far, Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, far}, target)))

def start_has(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +k: Nat)
  -> {optHas(startFlag(grammar, target, q, k), W.optsAt(grammar, target, q, k, 0n, k, F)) == True{} : Bool}:
  +s = startFlag(grammar, target, q, k)
  %Equal.sym(Bool, Nat.is_eq(k, k), True{}, Lemma.nat_eq_refl(k)) : {optHas(s, W.emptyPrefix(_, grammar, target, q, k)) == True{} : Bool}
  Lemma.or_true_left_intro(W.boolEq(s, s), False{}, bool_eq_refl(s))

def opt_d0(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +f: Bool,
  +h: {optHas(f, W.optsAt(grammar, target, q, ks, d, k, F)) == True{} : Bool}) -> {optHas(f, W.optsAt(grammar, target, q, ks, Nat.add(d, 0n), k, F)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 0n), d, Lemma.add_zero_right(d)) : {optHas(f, W.optsAt(grammar, target, q, ks, _, k, F)) == True{} : Bool}
  h

def opt_next(+grammar: +List<Core.Production>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +ks: Nat, +d: Nat, +n: Nat, +e: Nat, +f: Bool,
  +h: {optHas(f, W.optsAt(grammar, target, q, ks, Nat.add(1n+d, n), e, F)) == True{} : Bool}) -> {optHas(f, W.optsAt(grammar, target, q, ks, Nat.add(d, 1n+n), e, F)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 1n+n), 1n+Nat.add(d, n), Lemma.add_succ_right(d, n)) : {optHas(f, W.optsAt(grammar, target, q, ks, _, e, F)) == True{} : Bool}
  h

# A child's walk ends at its production's length and the node's end.
def child_conv(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +q2: Nat, +ch: +List<Core.Tree>, +k: Nat, +f: Bool,
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k) == True{} : Bool},
  +h: {optHas(f, W.optsAt(grammar, target, q2, k, Nat.add(0n, List.length(&2, Core.Tree, ch)), G.endOf(ch, k), F)) == True{} : Bool})
  -> {optHas(f, W.optsAt(grammar, target, q2, k, List.length(&2, Core.Sym, Core.rhsOf(grammar, q2)), Nat.add(k, Core.width(Core.Node{q2, ch})), F)) == True{} : Bool}:
  %PP.reads_length(ch, Core.rhsOf(grammar, q2), grammar, input, k, rc) : {optHas(f, W.optsAt(grammar, target, q2, k, _, Nat.add(k, Core.width(Core.Node{q2, ch})), F)) == True{} : Bool}
  %G.end_node(q2, ch, k) : {optHas(f, W.optsAt(grammar, target, q2, k, List.length(&2, Core.Tree, ch), _, F)) == True{} : Bool}
  h

# Walking a forest of kept steps: the segment after it has a fact with the rules' flag.
law wwalk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +cl: {closedW(ps, grammar, input, target, F) == True{} : Bool}
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +fd: Bool
  for +ie: {G.dropFrom(d, Core.rhsOf(grammar, q)) == items : +List<Core.Sym>}
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  for +iy: {Core.allIn(Core.own(q, f, d, ks, k), ps) == True{} : Bool}
  for +sy: {Core.allIn(Core.steps(f, k), ps) == True{} : Bool}
  for +hp: {optHas(fd, W.optsAt(grammar, target, q, ks, d, k, F)) == True{} : Bool}
  {optHas(cflag(f, grammar, target, q, ks, d, k, fd), W.optsAt(grammar, target, q, ks, Nat.add(d, List.length(&2, Core.Tree, f)), G.endOf(f, k), F)) == True{} : Bool}

def wwalk(f, items, grammar, input, ps, target, F, cl, q, ks, d, k, fd, ie, r, iy, sy, hp):
  match f items:
    case Nil{} Nil{}:
      opt_d0(grammar, target, F, q, ks, d, k, fd, hp)
    case Nil{} Con{+y, +yr}:
      Empty.absurd({optHas(fd, W.optsAt(grammar, target, q, ks, Nat.add(d, 0n), k, F)) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({optHas(cflag(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd), W.optsAt(grammar, target, q, ks, Nat.add(d, 1n+List.length(&2, Core.Tree, ts)), G.endOf(Core.Leaf{a} <> ts, k), F)) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({optHas(cflag(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd), W.optsAt(grammar, target, q, ks, Nat.add(d, 1n+List.length(&2, Core.Tree, ts)), G.endOf(Core.Leaf{a} <> ts, k), F)) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +r2 = Lemma.and_true_right_side(Nat.is_eq(a, t), more, r)
      +eq = Lemma.and_true_left(Nat.is_eq(a, t), more, r)
      +tok = Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), r2)
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), r2)
      +view = PP.leaf_view(q, d, ks, k, a, ts, ps, iy)
      +x = {Core.Bsr{q, 1n+d, ks, k, 1n+k} : Core.Bsr}
      +iyh = Lemma.and_true_left(Core.member(x, ps), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), ps), view)
      +iyt = Lemma.and_true_right_side(Core.member(x, ps), Core.allIn(Core.own(q, ts, 1n+d, ks, 1n+k), ps), view)
      +hi = item_at(grammar, input, target, F, q, d, Core.Terminal{t}, rest, k, 1n+k, False{}, ie, leaf_item(grammar, input, target, F, k, a, t, eq, tok))
      +f1 = {Bool.or(Bool.or(fd, False{}), Core.bsrEq(x, target)) : Bool}
      +hp1 = step_fact(grammar, input, ps, target, F, cl, q, ks, d, k, 1n+k, fd, False{}, hp, hi, iyh)
      opt_next(grammar, target, F, q, ks, d, List.length(&2, Core.Tree, ts), G.endOf(ts, 1n+k), cflag(ts, grammar, target, q, ks, 1n+d, 1n+k, f1),
        wwalk(ts, rest, grammar, input, ps, target, F, cl, q, ks, 1n+d, 1n+k, f1, G.drop_next(Core.rhsOf(grammar, q), d, Core.Terminal{t}, rest, ie), rt, iyt, sy, hp1))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd({optHas(cflag(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd), W.optsAt(grammar, target, q, ks, Nat.add(d, 1n+List.length(&2, Core.Tree, ts)), G.endOf(Core.Node{q2, ch} <> ts, k), F)) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({optHas(cflag(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd), W.optsAt(grammar, target, q, ks, Nat.add(d, 1n+List.length(&2, Core.Tree, ts)), G.endOf(Core.Node{q2, ch} <> ts, k), F)) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), r)
      +hd = Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), left)
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch})), hd)
      +nk = Lemma.and_true_right_side(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch})), hd)
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), left)
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), r)
      +step = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      +iyh = Lemma.and_true_left(Core.member(step, ps), Core.allIn(Core.own(q, ts, 1n+d, ks, far), ps), iy)
      +iyt = Lemma.and_true_right_side(Core.member(step, ps), Core.allIn(Core.own(q, ts, 1n+d, ks, far), ps), iy)
      +below = {List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)) : +List<Core.Bsr>}
      +syo = PP.in_app_left(Core.own(q2, ch, 0n, k, k), below, ps, sy)
      +syr = PP.in_app_right(Core.own(q2, ch, 0n, k, k), below, ps, sy)
      +syc = PP.in_app_left(Core.steps(ch, k), Core.steps(ts, far), ps, syr)
      +syt = PP.in_app_right(Core.steps(ch, k), Core.steps(ts, far), ps, syr)
      +fch = cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))
      +hc = child_conv(grammar, input, target, F, q2, ch, k, fch, rc,
        wwalk(ch, Core.rhsOf(grammar, q2), grammar, input, ps, target, F, cl, q2, k, 0n, k, startFlag(grammar, target, q2, k), {==}, rc, syo, syc, start_has(grammar, target, F, q2, k)))
      +hi = item_at(grammar, input, target, F, q, d, Core.Nonterminal{x, need}, rest, k, far, fch, ie, node_item(grammar, input, target, F, q2, ch, k, x, need, fch, lhs, nk, hc))
      +f1 = {Bool.or(Bool.or(fd, fch), Core.bsrEq(step, target)) : Bool}
      +hp1 = step_fact(grammar, input, ps, target, F, cl, q, ks, d, k, far, fd, fch, hp, hi, iyh)
      opt_next(grammar, target, F, q, ks, d, List.length(&2, Core.Tree, ts), G.endOf(ts, far), cflag(ts, grammar, target, q, ks, 1n+d, far, f1),
        wwalk(ts, rest, grammar, input, ps, target, F, cl, q, ks, 1n+d, far, f1, G.drop_next(Core.rhsOf(grammar, q), d, Core.Nonterminal{x, need}, rest, ie), rt, iyt, syt, hp1))

# ======== A TREE THAT CONTAINS THE TARGET GIVES A FLAG ========

# A node's own steps after its first child (`own` without the empty step).
def ownNE(+q: Nat, f: +List<Core.Tree>, +d: Nat, +ks: Nat, +k: Nat) -> +List<Core.Bsr>:
  match f:
    case Nil{}:
      []
    case Con{+t, rest}:
      Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(t))} <> ownNE(q, rest, 1n+d, ks, Nat.add(k, Core.width(t)))

law own_tail:
  for +q: Nat
  for f: +List<Core.Tree>
  for +d: Nat
  for +ks: Nat
  for +k: Nat
  {Core.own(q, f, 1n+d, ks, k) == ownNE(q, f, 1n+d, ks, k) : +List<Core.Bsr>}

def own_tail(q, f, d, ks, k):
  match f:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      +far = Nat.add(k, Core.width(t))
      Equal.cong(+List<Core.Bsr>, +List<Core.Bsr>, v => Core.Bsr{q, 2n+d, ks, k, far} <> v, Core.own(q, rest, 2n+d, ks, far), ownNE(q, rest, 2n+d, ks, far), own_tail(q, rest, 1n+d, ks, far))

def own_first(+q: Nat, +t: Core.Tree, +rest: +List<Core.Tree>, +d: Nat, +ks: Nat, +k: Nat)
  -> {Core.own(q, t <> rest, d, ks, k) == ownNE(q, t <> rest, d, ks, k) : +List<Core.Bsr>}:
  +far = Nat.add(k, Core.width(t))
  Equal.cong(+List<Core.Bsr>, +List<Core.Bsr>, v => Core.Bsr{q, 1n+d, ks, k, far} <> v, Core.own(q, rest, 1n+d, ks, far), ownNE(q, rest, 1n+d, ks, far), own_tail(q, rest, d, ks, far))

law mem_split:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +x: Core.Bsr
  for +h: {Core.member(x, List.append(&2, Core.Bsr, xs, ys)) == True{} : Bool}
  Either<{Core.member(x, xs) == True{} : Bool}, {Core.member(x, ys) == True{} : Bool}>

def split_more(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +ys: +List<Core.Bsr>,
  c: Either<{Core.member(x, rest) == True{} : Bool}, {Core.member(x, ys) == True{} : Bool}>)
  -> Either<{Core.member(x, y <> rest) == True{} : Bool}, {Core.member(x, ys) == True{} : Bool}>:
  match c:
    case Inl{m}:
      Inl{Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, rest), m)}
    case Inr{m}:
      Inr{m}

def split_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +ys: +List<Core.Bsr>,
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, List.append(&2, Core.Bsr, rest, ys)) == True{} : Bool}>,
  later: {Core.member(x, List.append(&2, Core.Bsr, rest, ys)) == True{} : Bool} -> Either<{Core.member(x, rest) == True{} : Bool}, {Core.member(x, ys) == True{} : Bool}>)
  -> Either<{Core.member(x, y <> rest) == True{} : Bool}, {Core.member(x, ys) == True{} : Bool}>:
  match cases:
    case Inl{e}:
      Inl{Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, rest), e)}
    case Inr{m}:
      split_more(x, y, rest, ys, later(m))

def mem_split(xs, ys, x, h):
  match xs:
    case Nil{}:
      Inr{h}
    case Con{+y, +rest}:
      split_pick(x, y, rest, ys, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, List.append(&2, Core.Bsr, rest, ys)), h), m => mem_split(rest, ys, x, m))

def bsr_flip(+a: Core.Bsr, +b: Core.Bsr, +h: {Core.bsrEq(a, b) == True{} : Bool}) -> {Core.bsrEq(b, a) == True{} : Bool}:
  %Equal.sym(Core.Bsr, a, b, G.bsr_eq_sound(a, b, h)) : {Core.bsrEq(b, _) == True{} : Bool}
  C.bsr_eq_refl(b)

law cflag_true:
  for f: +List<Core.Tree>
  for +grammar: +List<Core.Production>
  for +target: Core.Bsr
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  {cflag(f, grammar, target, q, ks, d, k, True{}) == True{} : Bool}

def cflag_true(f, grammar, target, q, ks, d, k):
  match f:
    case Nil{}:
      {==}
    case Con{Core.Leaf{+a}, +ts}:
      cflag_true(ts, grammar, target, q, ks, 1n+d, 1n+k)
    case Con{Core.Node{+q2, +ch}, +ts}:
      cflag_true(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})))

def cflag_at(+f: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool, +e: {fd == True{} : Bool})
  -> {cflag(f, grammar, target, q, ks, d, k, fd) == True{} : Bool}:
  %Equal.sym(Bool, fd, True{}, e) : {cflag(f, grammar, target, q, ks, d, k, _) == True{} : Bool}
  cflag_true(f, grammar, target, q, ks, d, k)

def or_r(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  Lemma.or_true_right_intro(a, b, h)

def or_l(+a: Bool, +b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  Lemma.or_true_left_intro(a, b, h)

def rhs_empty(items: +List<Core.Sym>, +grammar: +List<Core.Production>, +input: +List<Nat>, +k: Nat, +r: {Core.reads([], grammar, items, input, k) == True{} : Bool})
  -> {List.is_empty(&2, Core.Sym, items) == True{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(r))

def or_false(+a: Bool, +h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))

law mem_left:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +x: Core.Bsr
  for +h: {Core.member(x, xs) == True{} : Bool}
  {Core.member(x, List.append(&2, Core.Bsr, xs, ys)) == True{} : Bool}

def mem_left_pick(+x: Core.Bsr, +y: Core.Bsr, +rest: +List<Core.Bsr>, +ys: +List<Core.Bsr>,
  cases: Either<{Core.bsrEq(x, y) == True{} : Bool}, {Core.member(x, rest) == True{} : Bool}>,
  later: {Core.member(x, rest) == True{} : Bool} -> {Core.member(x, List.append(&2, Core.Bsr, rest, ys)) == True{} : Bool})
  -> {Core.member(x, y <> List.append(&2, Core.Bsr, rest, ys)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(Core.bsrEq(x, y), Core.member(x, List.append(&2, Core.Bsr, rest, ys)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, List.append(&2, Core.Bsr, rest, ys)), later(m))

def mem_left(xs, ys, x, h):
  match xs:
    case Nil{}:
      Empty.absurd({Core.member(x, ys) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+y, +rest}:
      mem_left_pick(x, y, rest, ys, Lemma.or_true_cases(Core.bsrEq(x, y), Core.member(x, rest), h), m => mem_left(rest, ys, x, m))

law mem_right:
  for xs: +List<Core.Bsr>
  for +ys: +List<Core.Bsr>
  for +x: Core.Bsr
  for +h: {Core.member(x, ys) == True{} : Bool}
  {Core.member(x, List.append(&2, Core.Bsr, xs, ys)) == True{} : Bool}

def mem_right(xs, ys, x, h):
  match xs:
    case Nil{}:
      h
    case Con{+y, +rest}:
      Lemma.or_true_right_intro(Core.bsrEq(x, y), Core.member(x, List.append(&2, Core.Bsr, rest, ys)), mem_right(rest, ys, x, h))

# Where the target can be: the flag so far, a node's own step, or a step below.
def Hit(f: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool) -> Type:
  Either<{fd == True{} : Bool}, Either<{Core.member(target, ownNE(q, f, d, ks, k)) == True{} : Bool}, {Core.member(target, Core.steps(f, k)) == True{} : Bool}>>

def own_mem(+q: Nat, +t: Core.Tree, +rest: +List<Core.Tree>, +k: Nat, +target: Core.Bsr,
  +m: {Core.member(target, Core.own(q, t <> rest, 0n, k, k)) == True{} : Bool}) -> {Core.member(target, ownNE(q, t <> rest, 0n, k, k)) == True{} : Bool}:
  %own_first(q, t, rest, 0n, k, k) : {Core.member(target, _) == True{} : Bool}
  m

def node_parts(+q2: Nat, +t: Core.Tree, +rest: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +k: Nat,
  c: Either<{Core.member(target, Core.own(q2, t <> rest, 0n, k, k)) == True{} : Bool}, {Core.member(target, Core.steps(t <> rest, k)) == True{} : Bool}>) -> Hit(t <> rest, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)):
  match c:
    case Inl{m}:
      Inr{Inl{own_mem(q2, t, rest, k, target, m)}}
    case Inr{m}:
      Inr{Inr{m}}

# A child node whose steps contain the target gets a true flag.
def node_flag(ch: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +q2: Nat, +k: Nat,
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k) == True{} : Bool},
  +h: {Core.member(target, List.append(&2, Core.Bsr, Core.own(q2, ch, 0n, k, k), Core.steps(ch, k))) == True{} : Bool},
  rec: Hit(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)) -> {cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)) == True{} : Bool})
  -> {cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)) == True{} : Bool}:
  match ch:
    case Nil{}:
      +b0 = {Core.Bsr{q2, 0n, k, k, k} : Core.Bsr}
      Lemma.and_true_intro(List.is_empty(&2, Core.Sym, Core.rhsOf(grammar, q2)), Core.bsrEq(b0, target), rhs_empty(Core.rhsOf(grammar, q2), grammar, input, k, rc),
        bsr_flip(target, b0, or_false(Core.bsrEq(target, b0), h)))
    case Con{+t, +rest}:
      rec(node_parts(q2, t, rest, grammar, target, k, mem_split(Core.own(q2, t <> rest, 0n, k, k), Core.steps(t <> rest, k), target, h)))

def leaf_mem(+q: Nat, +d: Nat, +ks: Nat, +k: Nat, +a: Nat, +ts: +List<Core.Tree>, +target: Core.Bsr,
  +m: {Core.member(target, ownNE(q, Core.Leaf{a} <> ts, d, ks, k)) == True{} : Bool}) -> {Core.member(target, Core.Bsr{q, 1n+d, ks, k, 1n+k} <> ownNE(q, ts, 1n+d, ks, 1n+k)) == True{} : Bool}:
  %Lemma.add_one_right(k) : {Core.member(target, Core.Bsr{q, 1n+d, ks, k, _} <> ownNE(q, ts, 1n+d, ks, _)) == True{} : Bool}
  m

def own_hit(+x: Core.Bsr, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d1: Nat, +k1: Nat, +f0: Bool,
  c: Either<{Core.bsrEq(target, x) == True{} : Bool}, {Core.member(target, ownNE(q, ts, d1, ks, k1)) == True{} : Bool}>,
  rec: Hit(ts, grammar, target, q, ks, d1, k1, Bool.or(f0, Core.bsrEq(x, target))) -> {cflag(ts, grammar, target, q, ks, d1, k1, Bool.or(f0, Core.bsrEq(x, target))) == True{} : Bool})
  -> {cflag(ts, grammar, target, q, ks, d1, k1, Bool.or(f0, Core.bsrEq(x, target))) == True{} : Bool}:
  match c:
    case Inl{e}:
      cflag_at(ts, grammar, target, q, ks, d1, k1, Bool.or(f0, Core.bsrEq(x, target)), or_r(f0, Core.bsrEq(x, target), bsr_flip(target, x, e)))
    case Inr{m}:
      rec(Inr{Inl{m}})

def leaf_more(+a: Nat, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool,
  hh: Either<{Core.member(target, ownNE(q, Core.Leaf{a} <> ts, d, ks, k)) == True{} : Bool}, {Core.member(target, Core.steps(Core.Leaf{a} <> ts, k)) == True{} : Bool}>,
  rec: Hit(ts, grammar, target, q, ks, 1n+d, 1n+k, Bool.or(Bool.or(fd, False{}), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, 1n+k}, target))) -> {cflag(ts, grammar, target, q, ks, 1n+d, 1n+k, Bool.or(Bool.or(fd, False{}), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, 1n+k}, target))) == True{} : Bool})
  -> {cflag(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}:
  match hh:
    case Inl{m}:
      +x = {Core.Bsr{q, 1n+d, ks, k, 1n+k} : Core.Bsr}
      own_hit(x, ts, grammar, target, q, ks, 1n+d, 1n+k, Bool.or(fd, False{}),
        Lemma.or_true_cases(Core.bsrEq(target, x), Core.member(target, ownNE(q, ts, 1n+d, ks, 1n+k)), leaf_mem(q, d, ks, k, a, ts, target, m)), rec)
    case Inr{m}:
      rec(Inr{Inr{m}})

def leaf_case(+a: Nat, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool,
  h: Hit(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd),
  rec: Hit(ts, grammar, target, q, ks, 1n+d, 1n+k, Bool.or(Bool.or(fd, False{}), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, 1n+k}, target))) -> {cflag(ts, grammar, target, q, ks, 1n+d, 1n+k, Bool.or(Bool.or(fd, False{}), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, 1n+k}, target))) == True{} : Bool})
  -> {cflag(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}:
  match h:
    case Inl{e}:
      cflag_at(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd, e)
    case Inr{hh}:
      leaf_more(a, ts, grammar, target, q, ks, d, k, fd, hh, rec)

def child_true(+ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +far: Nat, +fd: Bool, +fch: Bool, +here: Bool,
  +h: {fch == True{} : Bool}) -> {cflag(ts, grammar, target, q, ks, 1n+d, far, Bool.or(Bool.or(fd, fch), here)) == True{} : Bool}:
  cflag_at(ts, grammar, target, q, ks, 1n+d, far, Bool.or(Bool.or(fd, fch), here), or_l(Bool.or(fd, fch), here, or_r(fd, fch, h)))

def node_steps2(+q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool,
  c: Either<{Core.member(target, Core.steps(ch, k)) == True{} : Bool}, {Core.member(target, Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch})))) == True{} : Bool}>,
  recC: {Core.member(target, List.append(&2, Core.Bsr, Core.own(q2, ch, 0n, k, k), Core.steps(ch, k))) == True{} : Bool} -> {cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)) == True{} : Bool},
  recT: Hit(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) -> {cflag(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) == True{} : Bool})
  -> {cflag(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) == True{} : Bool}:
  match c:
    case Inl{m}:
      child_true(ts, grammar, target, q, ks, d, Nat.add(k, Core.width(Core.Node{q2, ch})), fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target),
        recC(mem_right(Core.own(q2, ch, 0n, k, k), Core.steps(ch, k), target, m)))
    case Inr{m}:
      recT(Inr{Inr{m}})

def node_steps1(+q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool,
  c: Either<{Core.member(target, Core.own(q2, ch, 0n, k, k)) == True{} : Bool}, {Core.member(target, List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch}))))) == True{} : Bool}>,
  recC: {Core.member(target, List.append(&2, Core.Bsr, Core.own(q2, ch, 0n, k, k), Core.steps(ch, k))) == True{} : Bool} -> {cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)) == True{} : Bool},
  recT: Hit(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) -> {cflag(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) == True{} : Bool})
  -> {cflag(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) == True{} : Bool}:
  match c:
    case Inl{m}:
      child_true(ts, grammar, target, q, ks, d, Nat.add(k, Core.width(Core.Node{q2, ch})), fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target),
        recC(mem_left(Core.own(q2, ch, 0n, k, k), Core.steps(ch, k), target, m)))
    case Inr{m}:
      node_steps2(q2, ch, ts, grammar, target, q, ks, d, k, fd, mem_split(Core.steps(ch, k), Core.steps(ts, Nat.add(k, Core.width(Core.Node{q2, ch}))), target, m), recC, recT)

def node_more(+q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool,
  hh: Either<{Core.member(target, ownNE(q, Core.Node{q2, ch} <> ts, d, ks, k)) == True{} : Bool}, {Core.member(target, Core.steps(Core.Node{q2, ch} <> ts, k)) == True{} : Bool}>,
  recC: {Core.member(target, List.append(&2, Core.Bsr, Core.own(q2, ch, 0n, k, k), Core.steps(ch, k))) == True{} : Bool} -> {cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)) == True{} : Bool},
  recT: Hit(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) -> {cflag(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) == True{} : Bool})
  -> {cflag(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}:
  match hh:
    case Inl{m}:
      +far = Nat.add(k, Core.width(Core.Node{q2, ch}))
      +x = {Core.Bsr{q, 1n+d, ks, k, far} : Core.Bsr}
      own_hit(x, ts, grammar, target, q, ks, 1n+d, far, Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))),
        Lemma.or_true_cases(Core.bsrEq(target, x), Core.member(target, ownNE(q, ts, 1n+d, ks, far)), m), recT)
    case Inr{m}:
      +far = Nat.add(k, Core.width(Core.Node{q2, ch}))
      node_steps1(q2, ch, ts, grammar, target, q, ks, d, k, fd,
        mem_split(Core.own(q2, ch, 0n, k, k), List.append(&2, Core.Bsr, Core.steps(ch, k), Core.steps(ts, far)), target, m), recC, recT)

def node_case(+q2: Nat, +ch: +List<Core.Tree>, +ts: +List<Core.Tree>, +grammar: +List<Core.Production>, +target: Core.Bsr, +q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool,
  h: Hit(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd),
  recC: {Core.member(target, List.append(&2, Core.Bsr, Core.own(q2, ch, 0n, k, k), Core.steps(ch, k))) == True{} : Bool} -> {cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k)) == True{} : Bool},
  recT: Hit(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) -> {cflag(ts, grammar, target, q, ks, 1n+d, Nat.add(k, Core.width(Core.Node{q2, ch})), Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target))) == True{} : Bool})
  -> {cflag(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}:
  match h:
    case Inl{e}:
      cflag_at(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd, e)
    case Inr{hh}:
      node_more(q2, ch, ts, grammar, target, q, ks, d, k, fd, hh, recC, recT)

# A forest whose steps (or flag so far) contain the target ends with a true flag.
law flag_walk:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +k: Nat
  for +fd: Bool
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  for h: Hit(f, grammar, target, q, ks, d, k, fd)
  {cflag(f, grammar, target, q, ks, d, k, fd) == True{} : Bool}

def nil_more(+fd: Bool, +target: Core.Bsr, hh: Either<{Core.member(target, []) == True{} : Bool}, {Core.member(target, []) == True{} : Bool}>) -> {fd == True{} : Bool}:
  match hh:
    case Inl{m}:
      Empty.absurd({fd == True{} : Bool}, Lemma.false_is_not_true(m))
    case Inr{m}:
      Empty.absurd({fd == True{} : Bool}, Lemma.false_is_not_true(m))

def nil_hit(+q: Nat, +ks: Nat, +d: Nat, +k: Nat, +fd: Bool, +grammar: +List<Core.Production>, +target: Core.Bsr, h: Hit([], grammar, target, q, ks, d, k, fd)) -> {fd == True{} : Bool}:
  match h:
    case Inl{e}:
      e
    case Inr{hh}:
      nil_more(fd, target, hh)

def flag_walk(f, items, grammar, input, target, q, ks, d, k, fd, r, h):
  match f items:
    case Nil{} Nil{}:
      nil_hit(q, ks, d, k, fd, grammar, target, h)
    case Nil{} Con{+y, +yr}:
      nil_hit(q, ks, d, k, fd, grammar, target, h)
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      +rt = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))
      +f1 = {Bool.or(Bool.or(fd, False{}), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, 1n+k}, target)) : Bool}
      leaf_case(a, ts, grammar, target, q, ks, d, k, fd, h, hit => flag_walk(ts, rest, grammar, input, target, q, ks, 1n+d, 1n+k, f1, rt, hit))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({cflag(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({cflag(Core.Leaf{a} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q2, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q2, x), Core.needOk(need, Core.width(Core.Node{q2, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads(ts, grammar, rest, input, far), r)
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q2), input, k), left)
      +rt = Lemma.and_true_right_side(own, Core.reads(ts, grammar, rest, input, far), r)
      +sf = startFlag(grammar, target, q2, k)
      node_case(q2, ch, ts, grammar, target, q, ks, d, k, fd, h,
        mm => node_flag(ch, grammar, input, target, q2, k, rc, mm, hit => flag_walk(ch, Core.rhsOf(grammar, q2), grammar, input, target, q2, k, 0n, k, sf, rc, hit)),
        hit => flag_walk(ts, rest, grammar, input, target, q, ks, 1n+d, far, Bool.or(Bool.or(fd, cflag(ch, grammar, target, q2, k, 0n, k, startFlag(grammar, target, q2, k))), Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, Nat.add(k, Core.width(Core.Node{q2, ch}))}, target)), rt, hit))
    case Con{Core.Node{+q2, +ch}, +ts} Nil{}:
      Empty.absurd({cflag(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q2, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({cflag(Core.Node{q2, ch} <> ts, grammar, target, q, ks, d, k, fd) == True{} : Bool}, Lemma.false_is_not_true(r))

# ======== THE ROOT ========

def root_mem2(+q: Nat, +ch: +List<Core.Tree>, +target: Core.Bsr,
  c: Either<{Core.member(target, Core.steps(ch, 0n)) == True{} : Bool}, {Core.member(target, []) == True{} : Bool}>) -> {Core.member(target, List.append(&2, Core.Bsr, Core.own(q, ch, 0n, 0n, 0n), Core.steps(ch, 0n))) == True{} : Bool}:
  match c:
    case Inl{m}:
      mem_right(Core.own(q, ch, 0n, 0n, 0n), Core.steps(ch, 0n), target, m)
    case Inr{m}:
      Empty.absurd({Core.member(target, List.append(&2, Core.Bsr, Core.own(q, ch, 0n, 0n, 0n), Core.steps(ch, 0n))) == True{} : Bool}, Lemma.false_is_not_true(m))

def root_mem(+q: Nat, +ch: +List<Core.Tree>, +target: Core.Bsr, +w: Nat,
  c: Either<{Core.member(target, Core.own(q, ch, 0n, 0n, 0n)) == True{} : Bool}, {Core.member(target, List.append(&2, Core.Bsr, Core.steps(ch, 0n), [])) == True{} : Bool}>)
  -> {Core.member(target, List.append(&2, Core.Bsr, Core.own(q, ch, 0n, 0n, 0n), Core.steps(ch, 0n))) == True{} : Bool}:
  match c:
    case Inl{m}:
      mem_left(Core.own(q, ch, 0n, 0n, 0n), Core.steps(ch, 0n), target, m)
    case Inr{m}:
      root_mem2(q, ch, target, mem_split(Core.steps(ch, 0n), [], target, m))

# The root node of a tree that contains the target gets a true flag.
def tree_flag(+q: Nat, +ch: +List<Core.Tree>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr,
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n) == True{} : Bool},
  +m: {Core.member(target, Core.steps([Core.Node{q, ch}], 0n)) == True{} : Bool}) -> {cflag(ch, grammar, target, q, 0n, 0n, 0n, startFlag(grammar, target, q, 0n)) == True{} : Bool}:
  +w = Nat.add(0n, Core.width(Core.Node{q, ch}))
  +sf = startFlag(grammar, target, q, 0n)
  node_flag(ch, grammar, input, target, q, 0n, rc,
    root_mem(q, ch, target, w, mem_split(Core.own(q, ch, 0n, 0n, 0n), List.append(&2, Core.Bsr, Core.steps(ch, 0n), []), target, m)),
    hit => flag_walk(ch, Core.rhsOf(grammar, q), grammar, input, target, q, 0n, 0n, 0n, sf, rc, hit))

def isTrees(m: Maybe<&2, +List<Core.Tree>>) -> Bool:
  match m:
    case Some{ts}:
      True{}
    case None{}:
      False{}

def flagged_head(f: Bool, +fo: +List<Core.Tree>, +later: Maybe<&2, +List<Core.Tree>>, +e: {W.boolEq(True{}, f) == True{} : Bool})
  -> {isTrees(W.flaggedPick(f, fo, later)) == True{} : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({isTrees(later) == True{} : Bool}, Lemma.false_is_not_true(e))

def flagged_tail(f: Bool, +fo: +List<Core.Tree>, +later: Maybe<&2, +List<Core.Tree>>, +h: {isTrees(later) == True{} : Bool})
  -> {isTrees(W.flaggedPick(f, fo, later)) == True{} : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      h

def first_pick(+f: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Opt>,
  cases: Either<{W.boolEq(True{}, f) == True{} : Bool}, {optHas(True{}, rest) == True{} : Bool}>,
  later: {optHas(True{}, rest) == True{} : Bool} -> {isTrees(W.firstFlagged(rest)) == True{} : Bool})
  -> {isTrees(W.flaggedPick(f, fo, W.firstFlagged(rest))) == True{} : Bool}:
  match cases:
    case Inl{e}:
      flagged_head(f, fo, W.firstFlagged(rest), e)
    case Inr{m}:
      flagged_tail(f, fo, W.firstFlagged(rest), later(m))

law first_has:
  for os: +List<W.Opt>
  for +h: {optHas(True{}, os) == True{} : Bool}
  {isTrees(W.firstFlagged(os)) == True{} : Bool}

def first_has(os, h):
  match os:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+f, +fo}, +rest}:
      first_pick(f, fo, rest, Lemma.or_true_cases(W.boolEq(True{}, f), optHas(True{}, rest), h), m => first_has(rest, m))

def nodeopt_pick(+q: Nat, +fl: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Opt>,
  cases: Either<{W.boolEq(True{}, fl) == True{} : Bool}, {optHas(True{}, rest) == True{} : Bool}>,
  later: {optHas(True{}, rest) == True{} : Bool} -> {optHas(True{}, W.nodeOpts(q, rest)) == True{} : Bool})
  -> {optHas(True{}, W.nodeOpts(q, W.Opt{fl, fo} <> rest)) == True{} : Bool}:
  match cases:
    case Inl{e}:
      Lemma.or_true_left_intro(W.boolEq(True{}, fl), optHas(True{}, W.nodeOpts(q, rest)), e)
    case Inr{m}:
      Lemma.or_true_right_intro(W.boolEq(True{}, fl), optHas(True{}, W.nodeOpts(q, rest)), later(m))

law node_opt_has:
  for +q: Nat
  for os: +List<W.Opt>
  for +h: {optHas(True{}, os) == True{} : Bool}
  {optHas(True{}, W.nodeOpts(q, os)) == True{} : Bool}

def node_opt_has(q, os, h):
  match os:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{W.Opt{+fl, +fo}, +rest}:
      nodeopt_pick(q, fl, fo, rest, Lemma.or_true_cases(W.boolEq(True{}, fl), optHas(True{}, rest), h), m => node_opt_has(q, rest, m))

def root_here(b: Bool, +grammar: +List<Core.Production>, +target: Core.Bsr, +base: Nat, +len: Nat, +n: Nat, +F: +List<W.Fact>,
  +eb: {b == True{} : Bool}, +h: {optHas(True{}, W.optsAt(grammar, target, base, 0n, len, n, F)) == True{} : Bool})
  -> {isTrees(W.rootPick(b, grammar, target, base, len, n, F)) == True{} : Bool}:
  match b:
    case True{}:
      first_has(W.nodeOpts(base, W.optsAt(grammar, target, base, 0n, len, n, F)), node_opt_has(base, W.optsAt(grammar, target, base, 0n, len, n, F), h))
    case False{}:
      Empty.absurd({isTrees(None{}) == True{} : Bool}, Lemma.false_is_not_true(eb))

def or_else_left(a: Maybe<&2, +List<Core.Tree>>, +b: Maybe<&2, +List<Core.Tree>>, +h: {isTrees(a) == True{} : Bool}) -> {isTrees(W.orElse(a, b)) == True{} : Bool}:
  match a:
    case Some{+x}:
      {==}
    case None{}:
      Empty.absurd({isTrees(b) == True{} : Bool}, Lemma.false_is_not_true(h))

def or_else_right(a: Maybe<&2, +List<Core.Tree>>, +b: Maybe<&2, +List<Core.Tree>>, +h: {isTrees(b) == True{} : Bool}) -> {isTrees(W.orElse(a, b)) == True{} : Bool}:
  match a:
    case Some{+x}:
      {==}
    case None{}:
      h

def rbase_zero(+grammar: +List<Core.Production>, +target: Core.Bsr, +base: Nat, +len: Nat, +n: Nat, +F: +List<W.Fact>,
  +h: {optHas(True{}, W.optsAt(grammar, target, Nat.add(base, 0n), 0n, len, n, F)) == True{} : Bool}) -> {optHas(True{}, W.optsAt(grammar, target, base, 0n, len, n, F)) == True{} : Bool}:
  %Lemma.add_zero_right(base) : {optHas(True{}, W.optsAt(grammar, target, _, 0n, len, n, F)) == True{} : Bool}
  h

def rbase_succ(+grammar: +List<Core.Production>, +target: Core.Bsr, +base: Nat, +m: Nat, +len: Nat, +n: Nat, +F: +List<W.Fact>,
  +h: {optHas(True{}, W.optsAt(grammar, target, Nat.add(base, 1n+m), 0n, len, n, F)) == True{} : Bool}) -> {optHas(True{}, W.optsAt(grammar, target, Nat.add(1n+base, m), 0n, len, n, F)) == True{} : Bool}:
  %Lemma.add_succ_right(base, m) : {optHas(True{}, W.optsAt(grammar, target, _, 0n, len, n, F)) == True{} : Bool}
  h

# A flagged forest at the root of a production of the start symbol is found.
law root_has:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +base: Nat
  for +grammar: +List<Core.Production>
  for +target: Core.Bsr
  for +n: Nat
  for +F: +List<W.Fact>
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  for +hi: {optHas(True{}, W.optsAt(grammar, target, Nat.add(base, q), 0n, List.length(&2, Core.Sym, Core.rhsOf(g, q)), n, F)) == True{} : Bool}
  {isTrees(W.rootFor(g, grammar, target, base, x, n, F)) == True{} : Bool}

def root_has(g, q, x, base, grammar, target, n, F, h, hi):
  match g q:
    case Nil{} +q0:
      Empty.absurd({False{} == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      +len = List.length(&2, Core.Sym, rhs)
      or_else_left(W.rootPick(Nat.is_eq(lhs, x), grammar, target, base, len, n, F), W.rootFor(rest, grammar, target, 1n+base, x, n, F),
        root_here(Nat.is_eq(lhs, x), grammar, target, base, len, n, F, h, rbase_zero(grammar, target, base, len, n, F, hi)))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+m):
      +len = List.length(&2, Core.Sym, rhs)
      or_else_right(W.rootPick(Nat.is_eq(lhs, x), grammar, target, base, len, n, F), W.rootFor(rest, grammar, target, 1n+base, x, n, F),
        root_has(rest, m, x, 1n+base, grammar, target, n, F, h, rbase_succ(grammar, target, base, m, List.length(&2, Core.Sym, Core.rhsOf(rest, m)), n, F, hi)))

def root_conv(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +q: Nat, +ch: +List<Core.Tree>, +f: Bool,
  +rc: {Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n) == True{} : Bool},
  +rl: {List.length(&2, Nat, Core.leaves([Core.Node{q, ch}])) == List.length(&2, Nat, input) : Nat},
  +h: {optHas(f, W.optsAt(grammar, target, q, 0n, Nat.add(0n, List.length(&2, Core.Tree, ch)), G.endOf(ch, 0n), F)) == True{} : Bool})
  -> {optHas(f, W.optsAt(grammar, target, q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, input), F)) == True{} : Bool}:
  %PP.reads_length(ch, Core.rhsOf(grammar, q), grammar, input, 0n, rc) : {optHas(f, W.optsAt(grammar, target, q, 0n, _, List.length(&2, Nat, input), F)) == True{} : Bool}
  %PP.leaves_end(q, ch, input, rl) : {optHas(f, W.optsAt(grammar, target, q, 0n, List.length(&2, Core.Tree, ch), _, F)) == True{} : Bool}
  h

def flag_at(+f: Bool, +os: +List<W.Opt>, +e: {f == True{} : Bool}, +h: {optHas(f, os) == True{} : Bool}) -> {optHas(True{}, os) == True{} : Bool}:
  %e : {optHas(_, os) == True{} : Bool}
  h

# WITNESS COMPLETENESS: on facts closed under the rules of ps, a parse tree made of steps of
# ps that contains the target gives the root search a forest.
law root_found:
  for tree: Core.Tree
  for +grammar: +List<Core.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ps: +List<Core.Bsr>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +cl: {closedW(ps, grammar, input, target, F) == True{} : Bool}
  for +inPs: {Core.allIn(Core.steps([tree], 0n), ps) == True{} : Bool}
  for +rr: {Core.reads([tree], grammar, [Core.Nonterminal{start, Core.Anything{}}], input, 0n) == True{} : Bool}
  for +rl: {List.length(&2, Nat, Core.leaves([tree])) == List.length(&2, Nat, input) : Nat}
  for +m: {Core.member(target, Core.steps([tree], 0n)) == True{} : Bool}
  {isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}

def root_found(tree, grammar, start, input, ps, target, F, cl, inPs, rr, rl, m):
  match tree:
    case Core.Leaf{+a}:
      Empty.absurd({isTrees(W.rootFor(grammar, grammar, target, 0n, start, List.length(&2, Nat, input), F)) == True{} : Bool}, Lemma.false_is_not_true(rr))
    case Core.Node{+q, +ch}:
      +w = {Core.width(Core.Node{q, ch}) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q, start), True{}) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n)) : Bool}
      +left = Lemma.and_true_left(own, Core.reads([], grammar, [], input, Nat.add(0n, w)), rr)
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, q, start), True{}, Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), left))
      +rc = Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, 0n), left)
      +below = {List.append(&2, Core.Bsr, Core.steps(ch, 0n), []) : +List<Core.Bsr>}
      +iyo = PP.in_app_left(Core.own(q, ch, 0n, 0n, 0n), below, ps, inPs)
      +syc = PP.in_app_left(Core.steps(ch, 0n), [], ps, PP.in_app_right(Core.own(q, ch, 0n, 0n, 0n), below, ps, inPs))
      +sf = startFlag(grammar, target, q, 0n)
      +fch = cflag(ch, grammar, target, q, 0n, 0n, 0n, sf)
      +hw = root_conv(grammar, input, target, F, q, ch, fch, rc, rl,
        wwalk(ch, Core.rhsOf(grammar, q), grammar, input, ps, target, F, cl, q, 0n, 0n, 0n, sf, {==}, rc, iyo, syc, start_has(grammar, target, F, q, 0n)))
      root_has(grammar, q, start, 0n, grammar, target, List.length(&2, Nat, input), F, lhs,
        flag_at(fch, W.optsAt(grammar, target, q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, input), F), tree_flag(q, ch, grammar, input, target, rc, m), hw))

# ======== THE FIXPOINT CLOSES ========
#
# A fact's key is counted as a descriptor, once per flag. A round either adds a fact with a
# key within bounds (one fewer unseen key) or changes nothing, and then the facts are closed.

def keyPick(b: Bool, +x: Gll.Desc, xs: +List<Gll.Desc>) -> +List<Gll.Desc>:
  match b:
    case True{}:
      x <> xs
    case False{}:
      xs

# The keys of the facts with this flag.
def keysOf(facts: +List<W.Fact>, +fl: Bool) -> +List<Gll.Desc>:
  match facts:
    case Nil{}:
      []
    case Con{W.Fact{+q, +ks, +d, +e, +fl2, fo}, rest}:
      keyPick(W.boolEq(fl, fl2), Gll.Desc{q, d, ks, e}, keysOf(rest, fl))

def fMeas(+grammar: +List<Core.Production>, +input: +List<Nat>, +facts: +List<W.Fact>) -> Nat:
  Nat.add(Run.countNot(Run.univ(grammar, input), keysOf(facts, True{})), Run.countNot(Run.univ(grammar, input), keysOf(facts, False{})))

def keysBnd(fs: +List<W.Fact>, +grammar: +List<Core.Production>, +input: +List<Nat>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{W.Fact{+q, +ks, +d, +e, fl, fo}, rest}:
      Bool.and(Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input), keysBnd(rest, grammar, input))

def and_t(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def key_true(+sk: Bool, +de: Bool, +h: Bool, +di: Bool, +e1: {sk == de : Bool}, +e2: {h == di : Bool})
  -> {Bool.or(Bool.and(sk, True{}), h) == Bool.or(de, di) : Bool}:
  %Equal.sym(Bool, Bool.and(sk, True{}), sk, and_t(sk)) : {Bool.or(_, h) == Bool.or(de, di) : Bool}
  %Equal.sym(Bool, sk, de, e1) : {Bool.or(_, h) == Bool.or(de, di) : Bool}
  %Equal.sym(Bool, h, di, e2) : {Bool.or(de, _) == Bool.or(de, di) : Bool}
  {==}

def key_false(+sk: Bool, +h: Bool, +di: Bool, +e2: {h == di : Bool}) -> {Bool.or(Bool.and(sk, False{}), h) == di : Bool}:
  %Equal.sym(Bool, Bool.and(sk, False{}), False{}, and_f(sk)) : {Bool.or(_, h) == di : Bool}
  e2

def key_case(b: Bool, +sk: Bool, +de: Bool, +h: Bool, +d: Gll.Desc, +d2: Gll.Desc, +ks: +List<Gll.Desc>,
  +e1: {sk == Gll.descEq(d, d2) : Bool}, +e2: {h == Gll.descIn(d, ks) : Bool})
  -> {Bool.or(Bool.and(sk, b), h) == Gll.descIn(d, keyPick(b, d2, ks)) : Bool}:
  match b:
    case True{}:
      key_true(sk, Gll.descEq(d, d2), h, Gll.descIn(d, ks), e1, e2)
    case False{}:
      key_false(sk, h, Gll.descIn(d, ks), e2)

# Having a fact is having its key among the keys of its flag.
law has_keys:
  for facts: +List<W.Fact>
  for +q: Nat
  for +ks: Nat
  for +d: Nat
  for +e: Nat
  for +fl: Bool
  {W.hasFact(q, ks, d, e, fl, facts) == Gll.descIn(Gll.Desc{q, d, ks, e}, keysOf(facts, fl)) : Bool}

def has_keys(facts, q, ks, d, e, fl):
  match facts:
    case Nil{}:
      {==}
    case Con{W.Fact{+q2, +ks2, +d2, +e2, +fl2, +fo}, +rest}:
      key_case(W.boolEq(fl, fl2), W.sameKey(q, ks, d, e, W.Fact{q2, ks2, d2, e2, fl2, fo}), True{}, W.hasFact(q, ks, d, e, fl, rest), Gll.Desc{q, d, ks, e}, Gll.Desc{q2, d2, ks2, e2}, keysOf(rest, fl),
        N.and_swap(Nat.is_eq(q, q2), Nat.is_eq(ks, ks2), Nat.is_eq(d, d2), Nat.is_eq(e, e2)), has_keys(rest, q, ks, d, e, fl))

def le_succ_add(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(Nat.add(a, 1n+b), c) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(a, b), c) == True{} : Bool}:
  %Lemma.add_succ_right(a, b) : {Nat.is_le(_, c) == True{} : Bool}
  h

# A new fact with a key within bounds: one fewer unseen key.
def meas_fact(+grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, fl: Bool, +fo: +List<Core.Tree>, +F: +List<W.Fact>,
  +out: {W.hasFact(q, ks, d, e, fl, F) == False{} : Bool}, +bd: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool})
  -> {Nat.is_le(1n+fMeas(grammar, input, W.Fact{q, ks, d, e, fl, fo} <> F), fMeas(grammar, input, F)) == True{} : Bool}:
  match fl:
    case True{}:
      +K = keysOf(F, True{})
      +o = Equal.trans(Bool, Gll.descIn(Gll.Desc{q, d, ks, e}, K), W.hasFact(q, ks, d, e, True{}, F), False{}, Equal.sym(Bool, W.hasFact(q, ks, d, e, True{}, F), Gll.descIn(Gll.Desc{q, d, ks, e}, K), has_keys(F, q, ks, d, e, True{})), out)
      C.le_add_l(1n+Run.countNot(Run.univ(grammar, input), Gll.Desc{q, d, ks, e} <> K), Run.countNot(Run.univ(grammar, input), K), Run.countNot(Run.univ(grammar, input), keysOf(F, False{})),
        C.count_drop(Run.univ(grammar, input), K, Gll.Desc{q, d, ks, e}, C.bound_mem(Gll.Desc{q, d, ks, e}, grammar, input, bd), o))
    case False{}:
      +K = keysOf(F, False{})
      +c1 = Run.countNot(Run.univ(grammar, input), keysOf(F, True{}))
      +o = Equal.trans(Bool, Gll.descIn(Gll.Desc{q, d, ks, e}, K), W.hasFact(q, ks, d, e, False{}, F), False{}, Equal.sym(Bool, W.hasFact(q, ks, d, e, False{}, F), Gll.descIn(Gll.Desc{q, d, ks, e}, K), has_keys(F, q, ks, d, e, False{})), out)
      le_succ_add(c1, Run.countNot(Run.univ(grammar, input), Gll.Desc{q, d, ks, e} <> K), Nat.add(c1, Run.countNot(Run.univ(grammar, input), K)),
        C.le_add_r(c1, 1n+Run.countNot(Run.univ(grammar, input), Gll.Desc{q, d, ks, e} <> K), Run.countNot(Run.univ(grammar, input), K),
          C.count_drop(Run.univ(grammar, input), K, Gll.Desc{q, d, ks, e}, C.bound_mem(Gll.Desc{q, d, ks, e}, grammar, input, bd), o)))

def AddSameB(+b: Bool, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Fact>, +F: +List<W.Fact>) -> Type:
  {W.addNew(rest, W.addPick(b, W.Fact{q, ks, d, e, f, fo}, F)) == F : +List<W.Fact>} & {Bool.and(W.hasFact(q, ks, d, e, f, F), factsIn(rest, F)) == True{} : Bool}

def AddResB(+b: Bool, +grammar: +List<Core.Production>, +input: +List<Nat>, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Fact>, +F: +List<W.Fact>) -> Type:
  Either<AddSameB(b, q, ks, d, e, f, fo, rest, F), {Nat.is_le(1n+fMeas(grammar, input, W.addNew(rest, W.addPick(b, W.Fact{q, ks, d, e, f, fo}, F))), fMeas(grammar, input, F)) == True{} : Bool}>

def AddSame(+new: +List<W.Fact>, +F: +List<W.Fact>) -> Type:
  {W.addNew(new, F) == F : +List<W.Fact>} & {factsIn(new, F) == True{} : Bool}

def AddRes(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<W.Fact>, +F: +List<W.Fact>) -> Type:
  Either<AddSame(new, F), {Nat.is_le(1n+fMeas(grammar, input, W.addNew(new, F)), fMeas(grammar, input, F)) == True{} : Bool}>

def add_le_eq2(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<W.Fact>, +F: +List<W.Fact>, +eq: {W.addNew(new, F) == F : +List<W.Fact>})
  -> {Nat.is_le(fMeas(grammar, input, W.addNew(new, F)), fMeas(grammar, input, F)) == True{} : Bool}:
  %Equal.sym(+List<W.Fact>, W.addNew(new, F), F, eq) : {Nat.is_le(fMeas(grammar, input, _), fMeas(grammar, input, F)) == True{} : Bool}
  Lemma.le_refl(fMeas(grammar, input, F))

def add_le_eq(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<W.Fact>, +F: +List<W.Fact>, p: {W.addNew(new, F) == F : +List<W.Fact>} & {factsIn(new, F) == True{} : Bool})
  -> {Nat.is_le(fMeas(grammar, input, W.addNew(new, F)), fMeas(grammar, input, F)) == True{} : Bool}:
  match p:
    case (+eq, fi):
      add_le_eq2(grammar, input, new, F, eq)

def add_le(+grammar: +List<Core.Production>, +input: +List<Nat>, +new: +List<W.Fact>, +F: +List<W.Fact>, r: AddRes(grammar, input, new, F)) -> {Nat.is_le(fMeas(grammar, input, W.addNew(new, F)), fMeas(grammar, input, F)) == True{} : Bool}:
  match r:
    case Inl{p}:
      add_le_eq(grammar, input, new, F, p)
    case Inr{m}:
      Lemma.le_of_succ_le(fMeas(grammar, input, W.addNew(new, F)), fMeas(grammar, input, F), m)

def add_known2(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Fact>, +grammar: +List<Core.Production>, +input: +List<Nat>, +F: +List<W.Fact>,
  +eb: {W.hasFact(q, ks, d, e, f, F) == True{} : Bool}, p: {W.addNew(rest, F) == F : +List<W.Fact>} & {factsIn(rest, F) == True{} : Bool})
  -> AddResB(True{}, grammar, input, q, ks, d, e, f, fo, rest, F):
  match p:
    case (+eq, fi):
      Inl{(eq, Lemma.and_true_intro(W.hasFact(q, ks, d, e, f, F), factsIn(rest, F), eb, fi))}

def add_known(+q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Fact>, +grammar: +List<Core.Production>, +input: +List<Nat>, +F: +List<W.Fact>,
  +eb: {W.hasFact(q, ks, d, e, f, F) == True{} : Bool}, r: AddRes(grammar, input, rest, F))
  -> AddResB(True{}, grammar, input, q, ks, d, e, f, fo, rest, F):
  match r:
    case Inl{p}:
      add_known2(q, ks, d, e, f, fo, rest, grammar, input, F, eb, p)
    case Inr{m}:
      Inr{m}

def add_pick(b: Bool, +q: Nat, +ks: Nat, +d: Nat, +e: Nat, +f: Bool, +fo: +List<Core.Tree>, +rest: +List<W.Fact>, +grammar: +List<Core.Production>, +input: +List<Nat>, +F: +List<W.Fact>,
  +eb: {W.hasFact(q, ks, d, e, f, F) == b : Bool},
  +bd: {Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input) == True{} : Bool},
  later: AddRes(grammar, input, rest, W.addPick(b, W.Fact{q, ks, d, e, f, fo}, F)))
  -> AddResB(b, grammar, input, q, ks, d, e, f, fo, rest, F):
  match b:
    case True{}:
      add_known(q, ks, d, e, f, fo, rest, grammar, input, F, eb, later)
    case False{}:
      +F1 = {W.Fact{q, ks, d, e, f, fo} <> F : +List<W.Fact>}
      Inr{Lemma.le_trans(1n+fMeas(grammar, input, W.addNew(rest, F1)), 1n+fMeas(grammar, input, F1), fMeas(grammar, input, F), add_le(grammar, input, rest, F1, later), meas_fact(grammar, input, q, ks, d, e, f, fo, F, eb, bd))}

# Adding facts with keys within bounds: nothing changes and they were there, or the count drops.
law add_new:
  for new: +List<W.Fact>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +F: +List<W.Fact>
  for +hb: {keysBnd(new, grammar, input) == True{} : Bool}
  AddRes(grammar, input, new, F)

def add_new(new, grammar, input, F, hb):
  match new:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{W.Fact{+q, +ks, +d, +e, +f, +fo}, +rest}:
      +bh = Lemma.and_true_left(Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input), keysBnd(rest, grammar, input), hb)
      +bt = Lemma.and_true_right_side(Run.descBound(Gll.Desc{q, d, ks, e}, grammar, input), keysBnd(rest, grammar, input), hb)
      +b = W.hasFact(q, ks, d, e, f, F)
      add_pick(b, q, ks, d, e, f, fo, rest, grammar, input, F, {==}, bh, add_new(rest, grammar, input, W.addPick(b, W.Fact{q, ks, d, e, f, fo}, F), bt))

def factsof_keys(os: +List<W.Opt>, +q: Nat, +ks: Nat, +dt: Nat, +e: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +bd: {Run.descBound(Gll.Desc{q, dt, ks, e}, grammar, input) == True{} : Bool}) -> {keysBnd(W.factsOf(q, ks, dt, e, os), grammar, input) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{W.Opt{+f, +fo}, +rest}:
      Lemma.and_true_intro(Run.descBound(Gll.Desc{q, dt, ks, e}, grammar, input), keysBnd(W.factsOf(q, ks, dt, e, rest), grammar, input), bd,
        factsof_keys(rest, q, ks, dt, e, grammar, input, bd))

# The facts a step within bounds makes have keys within bounds.
def step_keys(+grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, e: Core.Bsr, +hb: {Run.stepBound(e, grammar, input) == True{} : Bool})
  -> {keysBnd(W.stepFacts(grammar, input, target, F, e), grammar, input) == True{} : Bool}:
  match e:
    case Core.Bsr{+q, 0n, +ks, +k, +j}:
      {==}
    case Core.Bsr{+q, 1n+(+d), +ks, +k, +j}:
      +os = W.markIf(Core.bsrEq(Core.Bsr{q, 1n+d, ks, k, j}, target), W.joinAll(W.optsAt(grammar, target, q, ks, d, k, F), W.itemOpts(Gll.nthSym(Core.rhsOf(grammar, q), d), grammar, input, target, k, j, F)))
      factsof_keys(os, q, ks, 1n+d, j, grammar, input, Lemma.and_true_left(Run.descBound(Gll.Desc{q, 1n+d, ks, j}, grammar, input), Nat.is_le(k, List.length(&2, Nat, input)), hb))

def RoundSame(+ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>) -> Type:
  {W.roundOf(ps, grammar, input, target, F) == F : +List<W.Fact>} & {closedW(ps, grammar, input, target, F) == True{} : Bool}

def RoundRes(+ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>) -> Type:
  Either<RoundSame(ps, grammar, input, target, F), {Nat.is_le(1n+fMeas(grammar, input, W.roundOf(ps, grammar, input, target, F)), fMeas(grammar, input, F)) == True{} : Bool}>

def round_le_eq2(+ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, +eq: {W.roundOf(ps, grammar, input, target, F) == F : +List<W.Fact>})
  -> {Nat.is_le(fMeas(grammar, input, W.roundOf(ps, grammar, input, target, F)), fMeas(grammar, input, F)) == True{} : Bool}:
  %Equal.sym(+List<W.Fact>, W.roundOf(ps, grammar, input, target, F), F, eq) : {Nat.is_le(fMeas(grammar, input, _), fMeas(grammar, input, F)) == True{} : Bool}
  Lemma.le_refl(fMeas(grammar, input, F))

def round_le_eq(+ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, p: RoundSame(ps, grammar, input, target, F))
  -> {Nat.is_le(fMeas(grammar, input, W.roundOf(ps, grammar, input, target, F)), fMeas(grammar, input, F)) == True{} : Bool}:
  match p:
    case (+eq, cl):
      round_le_eq2(ps, grammar, input, target, F, eq)

def round_le(+ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, r: RoundRes(ps, grammar, input, target, F))
  -> {Nat.is_le(fMeas(grammar, input, W.roundOf(ps, grammar, input, target, F)), fMeas(grammar, input, F)) == True{} : Bool}:
  match r:
    case Inl{p}:
      round_le_eq(ps, grammar, input, target, F, p)
    case Inr{m}:
      Lemma.le_of_succ_le(fMeas(grammar, input, W.roundOf(ps, grammar, input, target, F)), fMeas(grammar, input, F), m)

def meas_to(+grammar: +List<Core.Production>, +input: +List<Nat>, +a: +List<W.Fact>, +b: +List<W.Fact>, +x: Nat, +eq: {a == b : +List<W.Fact>},
  +h: {Nat.is_le(1n+x, fMeas(grammar, input, a)) == True{} : Bool}) -> {Nat.is_le(1n+x, fMeas(grammar, input, b)) == True{} : Bool}:
  %eq : {Nat.is_le(1n+x, fMeas(grammar, input, _)) == True{} : Bool}
  h

def closed_to(+ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +a: +List<W.Fact>, +b: +List<W.Fact>, +eq: {a == b : +List<W.Fact>},
  +h: {closedW(ps, grammar, input, target, a) == True{} : Bool}) -> {closedW(ps, grammar, input, target, b) == True{} : Bool}:
  %eq : {closedW(ps, grammar, input, target, _) == True{} : Bool}
  h

def join_same2(+e: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>,
  +eq: {W.addNew(W.stepFacts(grammar, input, target, F, e), F) == F : +List<W.Fact>}, +fi: {factsIn(W.stepFacts(grammar, input, target, F, e), F) == True{} : Bool},
  q: RoundSame(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F))) -> RoundRes(e <> rest, grammar, input, target, F):
  match q:
    case (+eq2, cl):
      Inl{(Equal.trans(+List<W.Fact>, W.roundOf(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F)), W.addNew(W.stepFacts(grammar, input, target, F, e), F), F, eq2, eq),
        Lemma.and_true_intro(factsIn(W.stepFacts(grammar, input, target, F, e), F), closedW(rest, grammar, input, target, F), fi, closed_to(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F), F, eq, cl)))}

def join_same(+e: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>,
  +eq: {W.addNew(W.stepFacts(grammar, input, target, F, e), F) == F : +List<W.Fact>}, +fi: {factsIn(W.stepFacts(grammar, input, target, F, e), F) == True{} : Bool},
  r: RoundRes(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F))) -> RoundRes(e <> rest, grammar, input, target, F):
  match r:
    case Inl{q}:
      join_same2(e, rest, grammar, input, target, F, eq, fi, q)
    case Inr{m}:
      Inr{meas_to(grammar, input, W.addNew(W.stepFacts(grammar, input, target, F, e), F), F, fMeas(grammar, input, W.roundOf(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F))), eq, m)}

def join_added(+e: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>,
  p: AddSame(W.stepFacts(grammar, input, target, F, e), F), r: RoundRes(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F))) -> RoundRes(e <> rest, grammar, input, target, F):
  match p:
    case (+eq, fi):
      join_same(e, rest, grammar, input, target, F, eq, fi, r)

def round_join(+e: Core.Bsr, +rest: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>,
  a: AddRes(grammar, input, W.stepFacts(grammar, input, target, F, e), F), r: RoundRes(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F))) -> RoundRes(e <> rest, grammar, input, target, F):
  match a:
    case Inl{p}:
      join_added(e, rest, grammar, input, target, F, p, r)
    case Inr{m1}:
      Inr{Lemma.le_trans(1n+fMeas(grammar, input, W.roundOf(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F))), 1n+fMeas(grammar, input, W.addNew(W.stepFacts(grammar, input, target, F, e), F)), fMeas(grammar, input, F), round_le(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F), r), m1)}

# One round on steps within bounds: nothing changes and the facts are closed, or the count drops.
law round_res:
  for ps: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +hy: {Run.stepsBounded(ps, grammar, input) == True{} : Bool}
  RoundRes(ps, grammar, input, target, F)

def round_res(ps, grammar, input, target, F, hy):
  match ps:
    case Nil{}:
      Inl{({==}, {==})}
    case Con{+e, +rest}:
      +bh = Lemma.and_true_left(Run.stepBound(e, grammar, input), Run.stepsBounded(rest, grammar, input), hy)
      +bt = Lemma.and_true_right_side(Run.stepBound(e, grammar, input), Run.stepsBounded(rest, grammar, input), hy)
      round_join(e, rest, grammar, input, target, F, add_new(W.stepFacts(grammar, input, target, F, e), grammar, input, F, step_keys(grammar, input, target, F, e, bh)),
        round_res(rest, grammar, input, target, W.addNew(W.stepFacts(grammar, input, target, F, e), F), bt))

law fix_stays:
  for f: Nat
  for +ps: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +eq: {W.roundOf(ps, grammar, input, target, F) == F : +List<W.Fact>}
  {W.fixpoint(f, ps, grammar, input, target, F) == F : +List<W.Fact>}

def fix_stays(f, ps, grammar, input, target, F, eq):
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      %Equal.sym(+List<W.Fact>, W.roundOf(ps, grammar, input, target, F), F, eq) : {W.fixpoint(g, ps, grammar, input, target, _) == F : +List<W.Fact>}
      fix_stays(g, ps, grammar, input, target, F, eq)

def fix_same2(+f: Nat, +ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>,
  +eq: {W.roundOf(ps, grammar, input, target, F) == F : +List<W.Fact>}, +cl: {closedW(ps, grammar, input, target, F) == True{} : Bool}) -> {closedW(ps, grammar, input, target, W.fixpoint(f, ps, grammar, input, target, W.roundOf(ps, grammar, input, target, F))) == True{} : Bool}:
  %Equal.sym(+List<W.Fact>, W.roundOf(ps, grammar, input, target, F), F, eq) : {closedW(ps, grammar, input, target, W.fixpoint(f, ps, grammar, input, target, _)) == True{} : Bool}
  %Equal.sym(+List<W.Fact>, W.fixpoint(f, ps, grammar, input, target, F), F, fix_stays(f, ps, grammar, input, target, F, eq)) : {closedW(ps, grammar, input, target, _) == True{} : Bool}
  cl

def fix_same(+f: Nat, +ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, p: RoundSame(ps, grammar, input, target, F))
  -> {closedW(ps, grammar, input, target, W.fixpoint(f, ps, grammar, input, target, W.roundOf(ps, grammar, input, target, F))) == True{} : Bool}:
  match p:
    case (+eq, cl):
      fix_same2(f, ps, grammar, input, target, F, eq, cl)

def fix_step(+f: Nat, +ps: +List<Core.Bsr>, +grammar: +List<Core.Production>, +input: +List<Nat>, +target: Core.Bsr, +F: +List<W.Fact>, r: RoundRes(ps, grammar, input, target, F),
  +hf: {Nat.is_le(fMeas(grammar, input, F), f) == True{} : Bool},
  later: {Nat.is_le(1n+fMeas(grammar, input, W.roundOf(ps, grammar, input, target, F)), f) == True{} : Bool} -> {closedW(ps, grammar, input, target, W.fixpoint(f, ps, grammar, input, target, W.roundOf(ps, grammar, input, target, F))) == True{} : Bool})
  -> {closedW(ps, grammar, input, target, W.fixpoint(f, ps, grammar, input, target, W.roundOf(ps, grammar, input, target, F))) == True{} : Bool}:
  match r:
    case Inl{p}:
      fix_same(f, ps, grammar, input, target, F, p)
    case Inr{m}:
      later(Lemma.le_trans(1n+fMeas(grammar, input, W.roundOf(ps, grammar, input, target, F)), fMeas(grammar, input, F), f, m, hf))

# With more rounds than the count, the fixpoint ends closed.
law fix_closed:
  for fuel: Nat
  for +ps: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +F: +List<W.Fact>
  for +hy: {Run.stepsBounded(ps, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+fMeas(grammar, input, F), fuel) == True{} : Bool}
  {closedW(ps, grammar, input, target, W.fixpoint(fuel, ps, grammar, input, target, F)) == True{} : Bool}

def fix_closed(fuel, ps, grammar, input, target, F, hy, hf):
  match fuel:
    case 0n:
      Empty.absurd({closedW(ps, grammar, input, target, F) == True{} : Bool}, Lemma.false_is_not_true(hf))
    case 1n+(+f):
      fix_step(f, ps, grammar, input, target, F, round_res(ps, grammar, input, target, F, hy), hf,
        h2 => fix_closed(f, ps, grammar, input, target, W.roundOf(ps, grammar, input, target, F), hy, h2))

def start_meas(+fuel: Nat, +grammar: +List<Core.Production>, +input: +List<Nat>,
  +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool})
  -> {Nat.is_le(1n+fMeas(grammar, input, []), fuel) == True{} : Bool}:
  %Equal.sym(Nat, Run.countNot(Run.univ(grammar, input), []), List.length(&2, Gll.Desc, Run.univ(grammar, input)), C.count_empty(Run.univ(grammar, input))) : {Nat.is_le(1n+Nat.add(_, _), fuel) == True{} : Bool}
  hf

# THE WITNESS FACTS CLOSE: on steps within bounds, with fuel 1 + twice the size of the
# descriptor universe, the witness fixpoint ends closed.
law witness_closed:
  for +fuel: Nat
  for +ps: +List<Core.Bsr>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +target: Core.Bsr
  for +hy: {Run.stepsBounded(ps, grammar, input) == True{} : Bool}
  for +hf: {Nat.is_le(1n+Nat.add(List.length(&2, Gll.Desc, Run.univ(grammar, input)), List.length(&2, Gll.Desc, Run.univ(grammar, input))), fuel) == True{} : Bool}
  {closedW(ps, grammar, input, target, W.fixpoint(fuel, ps, grammar, input, target, [])) == True{} : Bool}

def witness_closed(fuel, ps, grammar, input, target, hy, hf):
  fix_closed(fuel, ps, grammar, input, target, [], hy, start_meas(fuel, grammar, input, hf))

