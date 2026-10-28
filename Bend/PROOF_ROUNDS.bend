import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check
import ./PRUNE.bend as Prune
import ./PROOF_GLL.bend as G
import ./FITS.bend as Fits
import ./LEMMAS.bend as Lemma

# THE ROUND RULE KEEPS EVERY STEP OF EVERY PARSE TREE.
#
# The rule (PRUNE.bend, roundRule) drops the link steps of rounds that break the
# empty-round rule. This proof walks a parse tree and shows that each of its link
# steps passes: in a parse tree, every round of a loop reads something, or it is the
# one round of a < > over nothing, at the loop's start. Other steps always pass.
#
# Also here, for the other proofs: the steps of every parse tree are among a set
# (StepsIn), and a few facts about lists of steps.

law rev_rev:
  for xs: +List<Nat>
  for +acc: +List<Nat>
  {Gll.reverseOnto(Gll.reverseOnto(xs, acc), []) == Gll.reverseOnto(acc, xs) : +List<Nat>}

def rev_rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      rev_rev(rest, x <> acc)

law step_rev:
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +d: Nat
  for pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  {Gll.reverseOnto(List.append(&2, Nat, prefix, [d]), []) == d <> rpath : +List<Nat>}

def step_rev(rpath, prefix, d, pEq):
  Equal.trans(+List<Nat>, Gll.reverseOnto(List.append(&2, Nat, prefix, [d]), []), Gll.reverseOnto(Gll.reverseOnto(rpath, [d]), []), d <> rpath,
    Equal.cong(+List<Nat>, +List<Nat>, v => Gll.reverseOnto(v, []), List.append(&2, Nat, prefix, [d]), Gll.reverseOnto(rpath, [d]), G.prefix_ext(rpath, prefix, [d], pEq)),
    rev_rev(rpath, [d]))

# Something read: the end is past the start.
law nonempty_lt:
  for xs: +List<Nat>
  for +pos: Nat
  for h: {Bool.not(List.is_empty(&2, Nat, List.append(&2, Nat, xs, []))) == True{} : Bool}
  {Nat.is_lt(pos, Nat.add(pos, List.length(&2, Nat, xs))) == True{} : Bool}

def nonempty_lt(xs, pos, h):
  match xs:
    case Nil{}:
      Empty.absurd({Nat.is_lt(pos, Nat.add(pos, 0n)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{x, +rest}:
      Lemma.lt_self_add(pos, List.length(&2, Nat, rest))

law in_head:
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for h: {Spec.allIn(x <> rest, ys) == True{} : Bool}
  {Spec.bsrMember(x, ys) == True{} : Bool}

def in_head(x, rest, ys, h):
  Lemma.and_true_left(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h)

law in_tail:
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for h: {Spec.allIn(x <> rest, ys) == True{} : Bool}
  {Spec.allIn(rest, ys) == True{} : Bool}

def in_tail(x, rest, ys, h):
  Lemma.and_true_right_side(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), h)

law in_app_left:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(xs, set) == True{} : Bool}

def in_app_left(xs, ys, set, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +both = h
      Lemma.and_true_intro(Spec.bsrMember(x, set), Spec.allIn(rest, set),
        Lemma.and_true_left(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, rest, ys), set), both),
        in_app_left(rest, ys, set, Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, rest, ys), set), both)))

law in_app_right:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +set: +List<Spec.Bsr>
  for h: {Spec.allIn(List.append(&2, Spec.Bsr, xs, ys), set) == True{} : Bool}
  {Spec.allIn(ys, set) == True{} : Bool}

def in_app_right(xs, ys, set, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      in_app_right(rest, ys, set, Lemma.and_true_right_side(Spec.bsrMember(x, set), Spec.allIn(List.append(&2, Spec.Bsr, rest, ys), set), h))

law positive_rounds:
  for rs: +List<Spec.Tree>
  for h: {Spec.roundsOk(Spec.Positive{}, rs) == True{} : Bool}
  {Bool.or(Spec.allConsume(rs), Nat.is_eq(List.length(&2, Spec.Tree, rs), 1n)) == True{} : Bool}

def positive_rounds(rs, h):
  match rs:
    case Nil{}:
      Empty.absurd({Bool.or(Spec.allConsume([]), Nat.is_eq(0n, 1n)) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{+r, +rr}:
      +n = List.length(&2, Spec.Tree, r <> rr)
      Lemma.and_true_right_side(Bool.not(Nat.is_lt(n, 1n)), Bool.or(Spec.allConsume(r <> rr), Nat.is_eq(n, 1n)), h)

# The rounds of a { } all read input; those of a < > too, or there is one.
law loop_cons:
  for kind: Spec.Bracket
  for rs: +List<Spec.Tree>
  for +pos: Nat
  for loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for h: {Spec.roundsOk(kind, rs) == True{} : Bool}
  {Bool.or(Spec.allConsume(rs), Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, pos), Nat.is_eq(List.length(&2, Spec.Tree, rs), 1n)))) == True{} : Bool}

def loop_cons(kind, rs, pos, loopOk, h):
  match kind rs:
    case Spec.Group{} _:
      Empty.absurd({Bool.or(Spec.allConsume(rs), Bool.and(Prune.isPositive(Spec.Group{}), Bool.and(Nat.is_eq(pos, pos), Nat.is_eq(List.length(&2, Spec.Tree, rs), 1n)))) == True{} : Bool}, Lemma.false_is_not_true(loopOk))
    case Spec.Optional{} _:
      Empty.absurd({Bool.or(Spec.allConsume(rs), Bool.and(Prune.isPositive(Spec.Optional{}), Bool.and(Nat.is_eq(pos, pos), Nat.is_eq(List.length(&2, Spec.Tree, rs), 1n)))) == True{} : Bool}, Lemma.false_is_not_true(loopOk))
    case Spec.Closure{} Nil{}:
      {==}
    case Spec.Closure{} Con{+r, +rr}:
      Lemma.or_true_left_intro(Spec.allConsume(r <> rr), Bool.and(Prune.isPositive(Spec.Closure{}), Bool.and(Nat.is_eq(pos, pos), Nat.is_eq(List.length(&2, Spec.Tree, r <> rr), 1n))), Lemma.or_false_right(Spec.allConsume(r <> rr), h))
    case Spec.Positive{} +rs2:
      +all = Spec.allConsume(rs2)
      +one = Nat.is_eq(List.length(&2, Spec.Tree, rs2), 1n)
      Lemma.or_mono_right(all, one, Bool.and(Prune.isPositive(Spec.Positive{}), Bool.and(Nat.is_eq(pos, pos), one)), positive_rounds(rs2, h),
        o => Lemma.and_true_intro(Nat.is_eq(pos, pos), one, Lemma.nat_eq_refl(pos), o))

law path_eq_refl:
  for xs: +List<Nat>
  {Spec.pathEq(xs, xs) == True{} : Bool}

def path_eq_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Lemma.and_true_intro(Nat.is_eq(x, x), Spec.pathEq(rest, rest), Lemma.nat_eq_refl(x), path_eq_refl(rest))

law bsr_member_head:
  for x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  {Spec.bsrMember(x, x <> rest) == True{} : Bool}

def bsr_member_head(x, rest):
  match x:
    case Spec.Bsr{Spec.Slot{+p, +path}, +i, +k, +j}:
      Lemma.or_true_left_intro(Bool.and(Nat.is_eq(p, p), Bool.and(Spec.pathEq(path, path), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))))), Spec.bsrMember(Spec.Bsr{Spec.Slot{p, path}, i, k, j}, rest),
        Lemma.and_true_intro(Nat.is_eq(p, p), Bool.and(Spec.pathEq(path, path), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)))), Lemma.nat_eq_refl(p),
          Lemma.and_true_intro(Spec.pathEq(path, path), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))), path_eq_refl(path),
            Lemma.and_true_intro(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)), Lemma.nat_eq_refl(i),
              Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(j, j), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(j))))))

law bsr_member_cons:
  for e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for m: {Spec.bsrMember(e, rest) == True{} : Bool}
  {Spec.bsrMember(e, x <> rest) == True{} : Bool}

def bsr_member_cons(e, x, rest, m):
  match e x:
    case Spec.Bsr{Spec.Slot{+p, +path}, +i, +k, +j} Spec.Bsr{Spec.Slot{p2, path2}, i2, k2, j2}:
      Lemma.or_true_right_intro(Bool.and(Nat.is_eq(p, p2), Bool.and(Spec.pathEq(path, path2), Bool.and(Nat.is_eq(i, i2), Bool.and(Nat.is_eq(k, k2), Nat.is_eq(j, j2))))), Spec.bsrMember(Spec.Bsr{Spec.Slot{p, path}, i, k, j}, rest), m)

# Every step of every parse tree is in ys.
def StepsIn(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +ys: +List<Spec.Bsr>) -> Type:
  @tree: Spec.Tree -> {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool} -> {Spec.leaves([tree]) == input : +List<Nat>} ->
    {Spec.allIn(Spec.steps(tree, 0n), ys) == True{} : Bool}

def FoundSteps(found: Maybe<&2, +List<Spec.Bsr>>, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>) -> Type:
  match found:
    case Some{+ys}:
      StepsIn(grammar, start, input, ys)
    case None{}:
      Unit

law checked_state:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +s: Gll.GState
  for +ys: +List<Spec.Bsr>
  for facts: {Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)) == True{} : Bool} & {Check.stepsOf(s) == ys : +List<Spec.Bsr>}
  for +tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  {Spec.allIn(Spec.steps(tree, 0n), ys) == True{} : Bool}

def checked_state(grammar, start, input, s, ys, facts, tree, fitting, spelled):
  match facts:
    case (ok0, same):
      +ok = {ok0 : {Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)) == True{} : Bool}}
      %same : {Spec.allIn(Spec.steps(tree, 0n), _) == True{} : Bool}
      G.closed_complete(grammar, start, input, s,
        Lemma.and_true_left(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s), ok),
        Lemma.and_true_right_side(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s), ok),
        tree, fitting, spelled)

# The checked parser's set has every step of every parse tree.
law checked_all_in:
  for r: Gll.GRun
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +ys: +List<Spec.Bsr>
  for got: {Check.runChecked(r, grammar, start, input) == Some{ys} : Maybe<&2, +List<Spec.Bsr>>}
  for +tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for spelled: {Spec.leaves([tree]) == input : +List<Nat>}
  {Spec.allIn(Spec.steps(tree, 0n), ys) == True{} : Bool}

def checked_all_in(r, grammar, start, input, ys, got, tree, fitting, spelled):
  match r:
    case Gll.GDone{+s}:
      checked_state(grammar, start, input, s, ys, G.check_pick(Bool.and(Check.closed(grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), s, ys, got), tree, fitting, spelled)
    case Gll.OutOfFuel{s}:
      Empty.absurd({Spec.allIn(Spec.steps(tree, 0n), ys) == True{} : Bool}, Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{ys}, got)))

law checked_run:
  for r: Gll.GRun
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +eq: {Check.runChecked(r, grammar, start, input) == found : Maybe<&2, +List<Spec.Bsr>>}
  FoundSteps(found, grammar, start, input)

def checked_run(r, grammar, start, input, found, eq):
  match found:
    case Some{+ys}:
      +tree => fitting => spelled => checked_all_in(r, grammar, start, input, ys, eq, tree, fitting, spelled)
    case None{}:
      Unit{}

# The checked parser's steps have every step of every parse tree.
law checked_found:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  FoundSteps(Check.checkedSteps(fuel, grammar, start, input), grammar, start, input)

def checked_found(fuel, grammar, start, input):
  +r = Gll.parse(fuel, grammar, start, input)
  checked_run(r, grammar, start, input, Check.runChecked(r, grammar, start, input), {==})

# ======== LINK STEPS ========

def allLink(xs: +List<Spec.Bsr>, +grammar: +List<Spec.Production>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(Prune.linkOk(grammar, x), allLink(rest, grammar))

# Where a tree that starts at pos ends, written as the walk writes it.
def endOf(t: Spec.Tree, +pos: Nat) -> Nat:
  match t:
    case Spec.Leaf{k}:
      1n+pos
    case Spec.Node{q, ch}:
      Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
    case Spec.Pick{a, ch}:
      Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
    case Spec.Skip{}:
      pos
    case Spec.Loop{rs}:
      Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs)))

# The link check of the first step of a forest that starts a sequence.
def firstTree(forest: +List<Spec.Tree>, +grammar: +List<Spec.Production>, +index: Nat, +rpath: +List<Nat>, +ctx: Nat, +pos: Nat) -> Bool:
  match forest:
    case Nil{}:
      True{}
    case Con{t, ts}:
      Prune.linkRest(rpath, grammar, index, ctx, pos, endOf(t, pos))

# Only a step at dot 1, the step of a sequence's first item, can be a link step.
def firstLink(dot: Nat, +forest: +List<Spec.Tree>, +grammar: +List<Spec.Production>, +index: Nat, +rpath: +List<Nat>, +ctx: Nat, +pos: Nat) -> Bool:
  match dot:
    case 0n:
      firstTree(forest, grammar, index, rpath, ctx, pos)
    case 1n+d:
      True{}

# The rounds of a loop from pos on: they all read something, or there is one, and it
# is a < > round at the loop's start.
def RoundsInv(+kind: Spec.Bracket, +ctx: Nat, +pos: Nat, +rs: +List<Spec.Tree>) -> Bool:
  Bool.or(Spec.allConsume(rs), Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, rs), 1n))))

law link_app:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for hx: {allLink(xs, grammar) == True{} : Bool}
  for +hy: {allLink(ys, grammar) == True{} : Bool}
  {allLink(List.append(&2, Spec.Bsr, xs, ys), grammar) == True{} : Bool}

def link_app(xs, ys, grammar, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      +both = hx
      Lemma.and_true_intro(Prune.linkOk(grammar, x), allLink(List.append(&2, Spec.Bsr, rest, ys), grammar),
        Lemma.and_true_left(Prune.linkOk(grammar, x), allLink(rest, grammar), both),
        link_app(rest, ys, grammar, Lemma.and_true_right_side(Prune.linkOk(grammar, x), allLink(rest, grammar), both), hy))

# The ε step at dot 0 is never a link step.
law link_dot0:
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +i: Nat
  for +k: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  {Prune.linkOk(grammar, Spec.at(index, prefix, 0n, i, k, k)) == True{} : Bool}

def link_dot0(rpath, prefix, grammar, index, i, k, pEq):
  %Equal.sym(+List<Nat>, Gll.reverseOnto(List.append(&2, Nat, prefix, [0n]), []), 0n <> rpath, step_rev(rpath, prefix, 0n, pEq)) : {Prune.linkAt(_, grammar, index, i, k, k) == True{} : Bool}
  {==}

# The step of the item at the dot passes: at dot 0 by what the sequence's start says,
# later because only dot 1 can hold a link step.
law link_head:
  for dot: Nat
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +ctx: Nat
  for +pos: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for first: {firstLink(dot, t <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}
  {Prune.linkOk(grammar, Spec.at(index, prefix, 1n+dot, ctx, pos, endOf(t, pos))) == True{} : Bool}

def link_head(dot, t, ts, rpath, prefix, grammar, index, ctx, pos, pEq, first):
  match dot:
    case 0n:
      %Equal.sym(+List<Nat>, Gll.reverseOnto(List.append(&2, Nat, prefix, [1n]), []), 1n <> rpath, step_rev(rpath, prefix, 1n, pEq)) : {Prune.linkAt(_, grammar, index, ctx, pos, endOf(t, pos)) == True{} : Bool}
      first
    case 1n+d:
      %Equal.sym(+List<Nat>, Gll.reverseOnto(List.append(&2, Nat, prefix, [1n+(1n+d)]), []), (1n+(1n+d)) <> rpath, step_rev(rpath, prefix, 1n+(1n+d), pEq)) : {Prune.linkAt(_, grammar, index, ctx, pos, endOf(t, pos)) == True{} : Bool}
      {==}

# A production's sequence starts no round.
law first_top:
  for ch: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +q: Nat
  for +ctx: Nat
  for +pos: Nat
  {firstTree(ch, grammar, q, [], ctx, pos) == True{} : Bool}

def first_top(ch, grammar, q, ctx, pos):
  match ch:
    case Nil{}:
      {==}
    case Con{t, ts}:
      {==}

# Nor does an alternative of a ( ) or [ ].
law first_pick:
  for ch: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +a: Nat
  for +dot: Nat
  for +rpath: +List<Nat>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ctx: Nat
  for +pos: Nat
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +notLoop: {Gll.isLoop(kind) == False{} : Bool}
  {firstTree(ch, grammar, index, a <> dot <> rpath, ctx, pos) == True{} : Bool}

def first_pick(ch, grammar, index, a, dot, rpath, kind, alts, ctx, pos, itemEq, notLoop):
  match ch:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +rest = Nat.is_eq(List.length(&2, Spec.Item, Spec.altOf(alts, a)), 1n)
      +ok = Prune.roundOk(kind, ctx, pos, endOf(t, pos))
      %Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{kind, alts}}, itemEq) : {Prune.linkItem(_, a, ctx, pos, endOf(t, pos)) == True{} : Bool}
      %Equal.sym(Bool, Gll.isLoop(kind), False{}, notLoop) : {Bool.or(Bool.not(Bool.and(_, rest)), ok) == True{} : Bool}
      {==}

# ---- One round ----

# Where a single tree ends, as the round's end.
law end_single:
  for t: Spec.Tree
  for +pos: Nat
  {endOf(t, pos) == Nat.add(pos, List.length(&2, Nat, Spec.leaves([t]))) : Nat}

def end_single(t, pos):
  match t:
    case Spec.Leaf{k}:
      Equal.sym(Nat, Nat.add(pos, 1n), 1n+pos, Lemma.add_one_right(pos))
    case Spec.Node{q, +ch}:
      Equal.cong(+List<Nat>, Nat, v => Nat.add(pos, List.length(&2, Nat, v)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Pick{a, +ch}:
      Equal.cong(+List<Nat>, Nat, v => Nat.add(pos, List.length(&2, Nat, v)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Skip{}:
      Equal.sym(Nat, Nat.add(pos, 0n), pos, Lemma.add_zero_right(pos))
    case Spec.Loop{+rs}:
      Equal.cong(+List<Nat>, Nat, v => Nat.add(pos, List.length(&2, Nat, v)), Spec.leaves(rs), List.append(&2, Nat, Spec.leaves(rs), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(rs), []), Spec.leaves(rs), Lemma.append_nil_right(Spec.leaves(rs))))

# A < > round at the loop's start is allowed, whatever it reads.
law pos_round:
  for xs: +List<Nat>
  for +kind: Spec.Bracket
  for +ctx: Nat
  for +pos: Nat
  for +posK: {Prune.isPositive(kind) == True{} : Bool}
  for +pc: {Nat.is_eq(pos, ctx) == True{} : Bool}
  {Prune.roundOk(kind, ctx, pos, Nat.add(pos, List.length(&2, Nat, xs))) == True{} : Bool}

def pos_round(xs, kind, ctx, pos, posK, pc):
  match xs:
    case Nil{}:
      +same = Prune.isPositive(kind)
      %Equal.sym(Nat, Nat.add(pos, 0n), pos, Lemma.add_zero_right(pos)) : {Bool.or(Nat.is_lt(pos, _), Bool.and(same, Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(_, ctx)))) == True{} : Bool}
      Lemma.or_true_right_intro(Nat.is_lt(pos, pos), Bool.and(same, Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(pos, ctx))),
        Lemma.and_true_intro(same, Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(pos, ctx)), posK, Lemma.and_true_intro(Nat.is_eq(pos, ctx), Nat.is_eq(pos, ctx), pc, pc)))
    case Con{x, +rest}:
      +e = Nat.add(pos, 1n+List.length(&2, Nat, rest))
      Lemma.or_true_left_intro(Nat.is_lt(pos, e), Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(e, ctx))), Lemma.lt_self_add(pos, List.length(&2, Nat, rest)))

law round_ok_cases:
  for +kind: Spec.Bracket
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for cases: Either<{Spec.allConsume(Spec.Pick{a, ch} <> rest) == True{} : Bool}, {Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), 1n))) == True{} : Bool}>
  {Prune.roundOk(kind, ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def round_ok_cases(kind, ctx, pos, a, ch, rest, cases):
  match cases:
    case Inl{all0}:
      +all = all0
      +e = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
      +cons = Lemma.and_true_left(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(rest), all)
      Lemma.or_true_left_intro(Nat.is_lt(pos, e), Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(e, ctx))), nonempty_lt(Spec.leaves(ch), pos, cons))
    case Inr{p0}:
      +p = p0
      +posK = Lemma.and_true_left(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), 1n)), p)
      +more = Lemma.and_true_right_side(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), 1n)), p)
      pos_round(Spec.leaves(ch), kind, ctx, pos, posK, Lemma.and_true_left(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), 1n), more))

# Every round of a parse tree's loop is allowed.
law round_ok:
  for +kind: Spec.Bracket
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for inv: {RoundsInv(kind, ctx, pos, Spec.Pick{a, ch} <> rest) == True{} : Bool}
  {Prune.roundOk(kind, ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}

def round_ok(kind, ctx, pos, a, ch, rest, inv):
  +rs = {Spec.Pick{a, ch} <> rest : +List<Spec.Tree>}
  round_ok_cases(kind, ctx, pos, a, ch, rest, Lemma.or_true_cases(Spec.allConsume(rs), Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, rs), 1n))), inv))

law next_single:
  for rest: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +ctx: Nat
  for +e: Nat
  for +one: {Nat.is_eq(List.length(&2, Spec.Tree, rest), 0n) == True{} : Bool}
  {RoundsInv(kind, ctx, e, rest) == True{} : Bool}

def next_single(rest, kind, ctx, e, one):
  match rest:
    case Nil{}:
      {==}
    case Con{r, rr}:
      Empty.absurd({RoundsInv(kind, ctx, e, r <> rr) == True{} : Bool}, Lemma.false_is_not_true(one))

law next_cases:
  for +kind: Spec.Bracket
  for +ctx: Nat
  for +pos: Nat
  for +e: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for cases: Either<{Spec.allConsume(Spec.Pick{a, ch} <> rest) == True{} : Bool}, {Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), 1n))) == True{} : Bool}>
  {RoundsInv(kind, ctx, e, rest) == True{} : Bool}

def next_cases(kind, ctx, pos, e, a, ch, rest, cases):
  match cases:
    case Inl{all0}:
      +all = all0
      +restAll = Lemma.and_true_right_side(Spec.consumes(Spec.Pick{a, ch}), Spec.allConsume(rest), all)
      Lemma.or_true_left_intro(Spec.allConsume(rest), Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(e, ctx), Nat.is_eq(List.length(&2, Spec.Tree, rest), 1n))), restAll)
    case Inr{p0}:
      +p = p0
      +more = Lemma.and_true_right_side(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), 1n)), p)
      next_single(rest, kind, ctx, e, Lemma.and_true_right_side(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), 1n), more))

# The rounds after a round: still only rounds that read something.
law rounds_next:
  for +kind: Spec.Bracket
  for +ctx: Nat
  for +pos: Nat
  for +e: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for inv: {RoundsInv(kind, ctx, pos, Spec.Pick{a, ch} <> rest) == True{} : Bool}
  {RoundsInv(kind, ctx, e, rest) == True{} : Bool}

def rounds_next(kind, ctx, pos, e, a, ch, rest, inv):
  +rs = {Spec.Pick{a, ch} <> rest : +List<Spec.Tree>}
  next_cases(kind, ctx, pos, e, a, ch, rest, Lemma.or_true_cases(Spec.allConsume(rs), Bool.and(Prune.isPositive(kind), Bool.and(Nat.is_eq(pos, ctx), Nat.is_eq(List.length(&2, Spec.Tree, rs), 1n))), inv))

law round_first_more:
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +ts2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ctx: Nat
  for +pos: Nat
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for fitCh: {Spec.fits(t <> t2 <> ts2, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  {Prune.linkItem(Some{Spec.Brack{kind, alts}}, a, ctx, pos, endOf(t, pos)) == True{} : Bool}

def round_first_more(t, t2, ts2, grammar, kind, alts, a, ctx, pos, loopOk, fitCh):
  +n = List.length(&2, Spec.Item, Spec.altOf(alts, a))
  +ok = Prune.roundOk(kind, ctx, pos, endOf(t, pos))
  +count = Fits.fits_count(t <> t2 <> ts2, grammar, Spec.altOf(alts, a), fitCh)
  %count : {Bool.or(Bool.not(Bool.and(Gll.isLoop(kind), Nat.is_eq(_, 1n))), ok) == True{} : Bool}
  %Equal.sym(Bool, Gll.isLoop(kind), True{}, loopOk) : {Bool.or(Bool.not(Bool.and(_, Nat.is_eq(1n+(1n+List.length(&2, Spec.Tree, ts2)), 1n))), ok) == True{} : Bool}
  {==}

law round_first_ts:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +grammar: +List<Spec.Production>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ctx: Nat
  for +pos: Nat
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for fitCh: {Spec.fits(t <> ts, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for rok: {Prune.roundOk(kind, ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(t <> ts)))) == True{} : Bool}
  {Prune.linkItem(Some{Spec.Brack{kind, alts}}, a, ctx, pos, endOf(t, pos)) == True{} : Bool}

def round_first_ts(ts, t, grammar, kind, alts, a, ctx, pos, loopOk, fitCh, rok):
  match ts:
    case Nil{}:
      +single = Bool.and(Gll.isLoop(kind), Nat.is_eq(List.length(&2, Spec.Item, Spec.altOf(alts, a)), 1n))
      +e = Nat.add(pos, List.length(&2, Nat, Spec.leaves([t])))
      %Equal.sym(Nat, endOf(t, pos), e, end_single(t, pos)) : {Bool.or(Bool.not(single), Prune.roundOk(kind, ctx, pos, _)) == True{} : Bool}
      Lemma.or_true_right_intro(Bool.not(single), Prune.roundOk(kind, ctx, pos, e), rok)
    case Con{+t2, +ts2}:
      round_first_more(t, t2, ts2, grammar, kind, alts, a, ctx, pos, loopOk, fitCh)

# The first step of a round: a link step if the alternative has one item, and then
# the round is allowed.
law round_first:
  for ch: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +a: Nat
  for +m: Nat
  for +outer: +List<Nat>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +ctx: Nat
  for +pos: Nat
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for rok: {Prune.roundOk(kind, ctx, pos, Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))) == True{} : Bool}
  {firstTree(ch, grammar, index, a <> m <> outer, ctx, pos) == True{} : Bool}

def round_first(ch, grammar, index, a, m, outer, kind, alts, ctx, pos, itemEq, loopOk, fitCh, rok):
  match ch:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      %Equal.sym(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq) : {Prune.linkItem(_, a, ctx, pos, endOf(t, pos)) == True{} : Bool}
      round_first_ts(ts, t, grammar, kind, alts, a, ctx, pos, loopOk, fitCh, rok)

# ======== THE WALK ========

# What the walk needs: in a sequence, the forest fits the items from the dot on, and the
# step of its first item passes; in the rounds of a loop, the rounds fit the loop's body
# and are allowed (RoundsInv).
def LReady(rounds: Bool, +grammar: +List<Spec.Production>, +forest: +List<Spec.Tree>, +index: Nat, +rpath: +List<Nat>, +dot: Nat, +ctx: Nat, +pos: Nat, +items: +List<Spec.Item>, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> Type:
  match rounds:
    case False{}:
      {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == items : +List<Spec.Item>} & {Spec.fits(forest, grammar, items) == True{} : Bool} & {firstLink(dot, forest, grammar, index, rpath, ctx, pos) == True{} : Bool}
    case True{}:
      {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Gll.isLoop(kind) == True{} : Bool} & {Spec.fits(forest, grammar, Spec.times(List.length(&2, Spec.Tree, forest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {RoundsInv(kind, ctx, pos, forest) == True{} : Bool}

# What the walk shows: every step passes the round rule.
def LWalked(rounds: Bool, +grammar: +List<Spec.Production>, +forest: +List<Spec.Tree>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +ctx: Nat, +pos: Nat) -> Type:
  {allLink(Spec.walk(forest, rounds, index, prefix, dot, ctx, pos), grammar) == True{} : Bool}

def LIH(+grammar: +List<Spec.Production>, +forest: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @dot: Nat -> @ctx: Nat -> @pos: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> LReady(rounds, grammar, forest, index, rpath, dot, ctx, pos, items, kind, alts) -> LWalked(rounds, grammar, forest, index, prefix, dot, ctx, pos)

# ---- The end of a sequence ----

law l_nil:
  for dot: Nat
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +ctx: Nat
  for +pos: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  LWalked(False{}, grammar, [], index, prefix, dot, ctx, pos)

def l_nil(dot, grammar, index, rpath, prefix, ctx, pos, pEq):
  match dot:
    case 0n:
      Lemma.and_true_intro(Prune.linkOk(grammar, Spec.at(index, prefix, 0n, ctx, pos, pos)), True{}, link_dot0(rpath, prefix, grammar, index, ctx, pos, pEq), {==})
    case 1n+d:
      {==}

# ---- A token, a skip ----

law l_leaf:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +first: {firstLink(dot, Spec.Leaf{k0} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos)

def l_leaf(grammar, index, rpath, prefix, dot, ctx, pos, k0, ts, rest, pEq, restEq, fitTs, first, ihTs):
  +head = Spec.at(index, prefix, 1n+dot, ctx, pos, 1n+pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, 1n+pos)
  Lemma.and_true_intro(Prune.linkOk(grammar, head), allLink(later, grammar), link_head(dot, Spec.Leaf{k0}, ts, rpath, prefix, grammar, index, ctx, pos, pEq, first),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, 1n+pos, rest, Spec.Group{}, [], pEq, (restEq, (fitTs, {==}))))

law l_skip:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +first: {firstLink(dot, Spec.Skip{} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos)

def l_skip(grammar, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, restEq, fitTs, first, ihTs):
  +head = Spec.at(index, prefix, 1n+dot, ctx, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, pos)
  Lemma.and_true_intro(Prune.linkOk(grammar, head), allLink(later, grammar), link_head(dot, Spec.Skip{}, ts, rpath, prefix, grammar, index, ctx, pos, pEq, first),
    ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, pos, rest, Spec.Group{}, [], pEq, (restEq, (fitTs, {==}))))

# ---- A nonterminal ----

law l_node:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +first: {firstLink(dot, Spec.Node{q, ch} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}
  for ihCh: LIH(grammar, ch)
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos)

def l_node(grammar, index, rpath, prefix, dot, ctx, pos, q, ch, ts, rest, pEq, restEq, fitCh, fitTs, first, ihCh, ihTs):
  +end = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
  +head = Spec.at(index, prefix, 1n+dot, ctx, pos, end)
  +inner = Spec.walk(ch, False{}, q, [], 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, end)
  Lemma.and_true_intro(Prune.linkOk(grammar, head), allLink(List.append(&2, Spec.Bsr, inner, later), grammar), link_head(dot, Spec.Node{q, ch}, ts, rpath, prefix, grammar, index, ctx, pos, pEq, first),
    link_app(inner, later, grammar,
      ihCh(False{}, q, [], [], 0n, pos, pos, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, ({==}, (fitCh, first_top(ch, grammar, q, pos, pos)))),
      ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, end, rest, Spec.Group{}, [], pEq, (restEq, (fitTs, {==})))))

# ---- A ( ) or [ ] that matched ----

law l_pick:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +notLoop: {Gll.isLoop(bkind) == False{} : Bool}
  for +first: {firstLink(dot, Spec.Pick{a, ch} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}
  for ihCh: LIH(grammar, ch)
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos)

def l_pick(grammar, index, rpath, prefix, dot, ctx, pos, a, ch, ts, bkind, balts, rest, pEq, itemEq, restEq, fitCh, fitTs, notLoop, first, ihCh, ihTs):
  +end = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
  +head = Spec.at(index, prefix, 1n+dot, ctx, pos, end)
  +inner = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, end)
  +remCh = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot), Some{Spec.Brack{bkind, balts}}, itemEq)
  Lemma.and_true_intro(Prune.linkOk(grammar, head), allLink(List.append(&2, Spec.Bsr, inner, later), grammar), link_head(dot, Spec.Pick{a, ch}, ts, rpath, prefix, grammar, index, ctx, pos, pEq, first),
    link_app(inner, later, grammar,
      ihCh(False{}, index, a <> dot <> rpath, List.append(&2, Nat, prefix, [dot, a]), 0n, pos, pos, Spec.altOf(balts, a), Spec.Group{}, [], G.prefix_ext(rpath, prefix, [dot, a], pEq),
        (remCh, (fitCh, first_pick(ch, grammar, index, a, dot, rpath, bkind, balts, pos, pos, itemEq, notLoop)))),
      ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, end, rest, Spec.Group{}, [], pEq, (restEq, (fitTs, {==})))))

# ---- A loop ----

law l_loop:
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +itemEq: {Gll.nthItem(Gll.seqAt(grammar, index, rpath), dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, Gll.seqAt(grammar, index, rpath)) == rest : +List<Spec.Item>}
  for +loopOk: {Gll.isLoop(bkind) == True{} : Bool}
  for +okRs: {Spec.roundsOk(bkind, rs) == True{} : Bool}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +first: {firstLink(dot, Spec.Loop{rs} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}
  for ihRs: LIH(grammar, rs)
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos)

def l_loop(grammar, index, rpath, prefix, dot, ctx, pos, rs, ts, bkind, balts, rest, pEq, itemEq, restEq, loopOk, okRs, fitRs, fitTs, first, ihRs, ihTs):
  +end = Nat.add(pos, List.length(&2, Nat, Spec.leaves(rs)))
  +head = Spec.at(index, prefix, 1n+dot, ctx, pos, end)
  +inner = Spec.walk(rs, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos)
  +later = Spec.walk(ts, False{}, index, prefix, 1n+dot, ctx, end)
  Lemma.and_true_intro(Prune.linkOk(grammar, head), allLink(List.append(&2, Spec.Bsr, inner, later), grammar), link_head(dot, Spec.Loop{rs}, ts, rpath, prefix, grammar, index, ctx, pos, pEq, first),
    link_app(inner, later, grammar,
      ihRs(True{}, index, dot <> rpath, List.append(&2, Nat, prefix, [dot]), 0n, pos, pos, [], bkind, balts, G.prefix_ext(rpath, prefix, [dot], pEq),
        (itemEq, (loopOk, (fitRs, loop_cons(bkind, rs, pos, loopOk, okRs))))),
      ihTs(False{}, index, rpath, prefix, 1n+dot, ctx, end, rest, Spec.Group{}, [], pEq, (restEq, (fitTs, {==})))))

# ---- One round of a loop ----

law l_round:
  for rpath: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: LReady(True{}, grammar, Spec.Pick{a, ch} <> rest, index, rpath, dot, ctx, pos, [], kind, alts)
  for ihCh: LIH(grammar, ch)
  for ihRest: LIH(grammar, rest)
  LWalked(True{}, grammar, Spec.Pick{a, ch} <> rest, index, prefix, dot, ctx, pos)

def l_round(rpath, a, ch, rest, grammar, index, prefix, dot, ctx, pos, kind, alts, pEq, ready, ihCh, ihRest):
  match rpath:
    case Nil{}:
      match ready:
        case (itemEq, more):
          Empty.absurd(LWalked(True{}, grammar, Spec.Pick{a, ch} <> rest, index, prefix, dot, ctx, pos), Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{kind, alts}}, itemEq)))
    case Con{+m, +outer}:
      match ready:
        case (itemEq0, (loopOk0, (fit0, inv0))):
          +itemEq = {itemEq0 : {Gll.nthItem(Gll.seqAt(grammar, index, outer), m) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}}
          +loopOk = {loopOk0 : {Gll.isLoop(kind) == True{} : Bool}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
          +inv = {inv0 : {RoundsInv(kind, ctx, pos, Spec.Pick{a, ch} <> rest) == True{} : Bool}}
          +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
          +tm = Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})
          +fitCh = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_left(h, Spec.fits(rest, grammar, tm), fit))
          +fitRest = Lemma.and_true_right_side(h, Spec.fits(rest, grammar, tm), fit)
          +end = Nat.add(pos, List.length(&2, Nat, Spec.leaves(ch)))
          +inner = Spec.walk(ch, False{}, index, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos)
          +later = Spec.walk(rest, True{}, index, prefix, 0n, ctx, end)
          +remCh = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq)
          link_app(inner, later, grammar,
            ihCh(False{}, index, a <> m <> outer, List.append(&2, Nat, prefix, [a]), 0n, ctx, pos, Spec.altOf(alts, a), Spec.Group{}, [], G.prefix_ext(m <> outer, prefix, [a], pEq),
              (remCh, (fitCh, round_first(ch, grammar, index, a, m, outer, kind, alts, ctx, pos, itemEq, loopOk, fitCh, round_ok(kind, ctx, pos, a, ch, rest, inv))))),
            ihRest(True{}, index, m <> outer, prefix, 0n, ctx, end, [], kind, alts, pEq, (itemEq, (loopOk, (fitRest, rounds_next(kind, ctx, pos, end, a, ch, rest, inv))))))

# ---- Which tree meets which item ----

law lleaf_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +k0: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: LReady(False{}, grammar, Spec.Leaf{k0} <> ts, index, rpath, dot, ctx, pos, items, Spec.Group{}, [])
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos)
def lleaf_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, k0, ts, pEq, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Terminal{t}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Leaf{k0} <> ts, grammar, Spec.Sym{Spec.Terminal{t}} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Leaf{k0} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Terminal{t}}, rest, rem)
          l_leaf(grammar, index, rpath, prefix, dot, ctx, pos, k0, ts, rest, pEq, restEq, Fits.fits_tail(Spec.Leaf{k0}, ts, grammar, Spec.Sym{Spec.Terminal{t}}, rest, fit), first, ihTs)
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Leaf{k0} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law lnode_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: LReady(False{}, grammar, Spec.Node{q, ch} <> ts, index, rpath, dot, ctx, pos, items, Spec.Group{}, [])
  for ihCh: LIH(grammar, ch)
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos)
def lnode_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, q, ch, ts, pEq, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Sym{Spec.Nonterminal{x}} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Node{q, ch} <> ts, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Node{q, ch} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Sym{Spec.Nonterminal{x}}, rest, rem)
          +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          l_node(grammar, index, rpath, prefix, dot, ctx, pos, q, ch, ts, rest, pEq, restEq,
            Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)),
            Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit), first, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Node{q, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law lpick_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: LReady(False{}, grammar, Spec.Pick{a, ch} <> ts, index, rpath, dot, ctx, pos, items, Spec.Group{}, [])
  for ihCh: LIH(grammar, ch)
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos)
def lpick_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, a, ch, ts, pEq, ready, ihCh, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Group{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, balts} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Pick{a, ch} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Group{}, balts}, rest, rem)
          +h = Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          l_pick(grammar, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Group{}, balts, rest, pEq, itemEq, restEq,
            Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)),
            Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit), {==}, first, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Pick{a, ch} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +h0 = Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(balts, a))
          +h1 = Bool.and(h0, Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hk = Lemma.and_true_left(h1, Spec.fits(ts, grammar, rest), fit)
          l_pick(grammar, index, rpath, prefix, dot, ctx, pos, a, ch, ts, Spec.Optional{}, balts, rest, pEq, itemEq, restEq,
            Lemma.and_true_right_side(h0, Spec.fits(ch, grammar, Spec.altOf(balts, a)), hk),
            Lemma.and_true_right_side(h1, Spec.fits(ts, grammar, rest), fit), {==}, first, ihCh, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Pick{a, ch} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

law lskip_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: LReady(False{}, grammar, Spec.Skip{} <> ts, index, rpath, dot, ctx, pos, items, Spec.Group{}, [])
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos)
def lskip_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, ts, pEq, ready, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Optional{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Optional{}, balts} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Skip{} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Optional{}, balts}, rest, rem)
          l_skip(grammar, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, restEq, fit, first, ihTs)
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Skip{} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Eps{} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Skip{} <> ts, grammar, Spec.Eps{} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Skip{} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Eps{}, rest, rem)
          l_skip(grammar, index, rpath, prefix, dot, ctx, pos, ts, rest, pEq, restEq, fit, first, ihTs)

law lloop_disp:
  for items: +List<Spec.Item>
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: LReady(False{}, grammar, Spec.Loop{rs} <> ts, index, rpath, dot, ctx, pos, items, Spec.Group{}, [])
  for ihRs: LIH(grammar, rs)
  for ihTs: LIH(grammar, ts)
  LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos)
def lloop_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, rs, ts, pEq, ready, ihRs, ihTs):
  match items:
    case Nil{}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Terminal{+t}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Group{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))
    case Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Closure{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Closure{}, balts} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Loop{rs} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Closure{}, balts}, rest, rem)
          +tm = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})
          +h = Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tm))
          +hk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)
          l_loop(grammar, index, rpath, prefix, dot, ctx, pos, rs, ts, Spec.Closure{}, balts, rest, pEq, itemEq, restEq, {==},
            Lemma.and_true_left(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tm), hk), Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tm), hk),
            Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit), first, ihRs, ihTs)
    case Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          +rem = {rem0 : {G.dropItems(dot, Gll.seqAt(grammar, index, rpath)) == Spec.Brack{Spec.Positive{}, balts} <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(Spec.Loop{rs} <> ts, grammar, Spec.Brack{Spec.Positive{}, balts} <> rest) == True{} : Bool}}
          +first = {first0 : {firstLink(dot, Spec.Loop{rs} <> ts, grammar, index, rpath, ctx, pos) == True{} : Bool}}
          +itemEq = G.drop_next(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +restEq = G.drop_succ(dot, Gll.seqAt(grammar, index, rpath), Spec.Brack{Spec.Positive{}, balts}, rest, rem)
          +tm = Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})
          +h = Bool.and(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tm))
          +hk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)
          l_loop(grammar, index, rpath, prefix, dot, ctx, pos, rs, ts, Spec.Positive{}, balts, rest, pEq, itemEq, restEq, {==},
            Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tm), hk), Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, rs), Spec.fits(rs, grammar, tm), hk),
            Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit), first, ihRs, ihTs)
    case Con{Spec.Eps{}, +rest}:
      match ready:
        case (rem0, (fit0, first0)):
          Empty.absurd(LWalked(False{}, grammar, Spec.Loop{rs} <> ts, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit0))

# ---- The walk ----

law lwalk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
  for +grammar: +List<Spec.Production>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +dot: Nat
  for +ctx: Nat
  for +pos: Nat
  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for ready: LReady(rounds, grammar, forest, index, rpath, dot, ctx, pos, items, kind, alts)
  LWalked(rounds, grammar, forest, index, prefix, dot, ctx, pos)

def lwalk(forest, rounds, grammar, index, rpath, prefix, dot, ctx, pos, items, kind, alts, pEq, ready):
  match forest rounds:
    case Nil{} False{}:
      l_nil(dot, grammar, index, rpath, prefix, ctx, pos, pEq)
    case Nil{} True{}:
      {==}
    case Con{Spec.Leaf{+k0}, +ts} False{}:
      lleaf_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, k0, ts, pEq, ready,
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ts, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)))
    case Con{Spec.Node{+q, +ch}, +ts} False{}:
      lnode_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, q, ch, ts, pEq, ready,
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ch, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)),
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ts, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)))
    case Con{Spec.Pick{+a, +ch}, +ts} False{}:
      lpick_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, a, ch, ts, pEq, ready,
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ch, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)),
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ts, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)))
    case Con{Spec.Skip{}, +ts} False{}:
      lskip_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, ts, pEq, ready,
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ts, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)))
    case Con{Spec.Loop{+rs}, +ts} False{}:
      lloop_disp(items, grammar, index, rpath, prefix, dot, ctx, pos, rs, ts, pEq, ready,
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(rs, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)),
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ts, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)))
    case Con{Spec.Pick{+a, +ch}, +rest} True{}:
      l_round(rpath, a, ch, rest, grammar, index, prefix, dot, ctx, pos, kind, alts, pEq, ready,
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(ch, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)),
        (ri => ix => rx => px => dx => cx => qx => its => kx => ax => pe => rd => lwalk(rest, ri, grammar, ix, rx, px, dx, cx, qx, its, kx, ax, pe, rd)))
    case Con{Spec.Leaf{k0}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, inv))):
          Empty.absurd(LWalked(True{}, grammar, Spec.Leaf{k0} <> rest, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Node{q, ch}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, inv))):
          Empty.absurd(LWalked(True{}, grammar, Spec.Node{q, ch} <> rest, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Skip{}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, inv))):
          Empty.absurd(LWalked(True{}, grammar, Spec.Skip{} <> rest, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))
    case Con{Spec.Loop{rs}, rest} True{}:
      match ready:
        case (ie, (lo, (fit, inv))):
          Empty.absurd(LWalked(True{}, grammar, Spec.Loop{rs} <> rest, index, prefix, dot, ctx, pos), Lemma.false_is_not_true(fit))

# Every step of a parse tree passes the round rule.
law tree_links:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for tree: Spec.Tree
  for fitting: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  {allLink(Spec.steps(tree, 0n), grammar) == True{} : Bool}

def tree_links(grammar, start, tree, fitting):
  match tree:
    case Spec.Node{+q, +ch}:
      +h = Bool.and(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
      +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, start), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), Lemma.and_true_left(h, True{}, fitting))
      lwalk(ch, False{}, grammar, q, [], [], 0n, 0n, 0n, Spec.rhsOf(grammar, q), Spec.Group{}, [], {==}, ({==}, (fitCh, first_top(ch, grammar, q, 0n, 0n))))
    case Spec.Leaf{k}:
      Empty.absurd({allLink(Spec.steps(Spec.Leaf{k}, 0n), grammar) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Pick{a, ch}:
      Empty.absurd({allLink(Spec.steps(Spec.Pick{a, ch}, 0n), grammar) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Skip{}:
      Empty.absurd({allLink(Spec.steps(Spec.Skip{}, 0n), grammar) == True{} : Bool}, Lemma.false_is_not_true(fitting))
    case Spec.Loop{rs}:
      Empty.absurd({allLink(Spec.steps(Spec.Loop{rs}, 0n), grammar) == True{} : Bool}, Lemma.false_is_not_true(fitting))

# ======== THE RULE KEEPS THEM ========

law keep_link_head:
  for k: Bool
  for +isK: {k == True{} : Bool}
  for +x: Spec.Bsr
  for +others: +List<Spec.Bsr>
  {Spec.bsrMember(x, Prune.keepPick(k, x, others)) == True{} : Bool}

def keep_link_head(k, isK, x, others):
  match k:
    case True{}:
      bsr_member_head(x, others)
    case False{}:
      Empty.absurd({Spec.bsrMember(x, others) == True{} : Bool}, Lemma.false_is_not_true(isK))

law keep_link_later:
  for k: Bool
  for +x: Spec.Bsr
  for +others: +List<Spec.Bsr>
  for e: Spec.Bsr
  for m: {Spec.bsrMember(e, others) == True{} : Bool}
  {Spec.bsrMember(e, Prune.keepPick(k, x, others)) == True{} : Bool}

def keep_link_later(k, x, others, e, m):
  match k:
    case True{}:
      bsr_member_cons(e, x, others, m)
    case False{}:
      m

law keep_link_pick:
  for +grammar: +List<Spec.Production>
  for +e: Spec.Bsr
  for +x: Spec.Bsr
  for +rest: +List<Spec.Bsr>
  for cases: Either<{e == x : Spec.Bsr}, {Spec.bsrMember(e, rest) == True{} : Bool}>
  for +ok: {Prune.linkOk(grammar, e) == True{} : Bool}
  for searchRest: {Spec.bsrMember(e, rest) == True{} : Bool} -> {Spec.bsrMember(e, Prune.keepLinks(rest, grammar)) == True{} : Bool}
  {Spec.bsrMember(e, Prune.keepPick(Prune.linkOk(grammar, x), x, Prune.keepLinks(rest, grammar))) == True{} : Bool}

def keep_link_pick(grammar, e, x, rest, cases, ok, searchRest):
  match cases:
    case Inl{same}:
      +eq = same
      +others = Prune.keepLinks(rest, grammar)
      okX = Equal.trans(Bool, Prune.linkOk(grammar, x), Prune.linkOk(grammar, e), True{}, Equal.sym(Bool, Prune.linkOk(grammar, e), Prune.linkOk(grammar, x), Equal.cong(Spec.Bsr, Bool, v => Prune.linkOk(grammar, v), e, x, eq)), ok)
      %Equal.sym(Spec.Bsr, e, x, eq) : {Spec.bsrMember(_, Prune.keepPick(Prune.linkOk(grammar, x), x, others)) == True{} : Bool}
      keep_link_head(Prune.linkOk(grammar, x), okX, x, others)
    case Inr{later}:
      keep_link_later(Prune.linkOk(grammar, x), x, Prune.keepLinks(rest, grammar), e, searchRest(later))

# A step of the set that passes the rule stays.
law keep_link_member:
  for ys: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for +e: Spec.Bsr
  for m: {Spec.bsrMember(e, ys) == True{} : Bool}
  for +ok: {Prune.linkOk(grammar, e) == True{} : Bool}
  {Spec.bsrMember(e, Prune.keepLinks(ys, grammar)) == True{} : Bool}

def keep_link_member(ys, grammar, e, m, ok):
  match ys:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(e, []) == True{} : Bool}, G.ebnf_not_in_empty(e, m))
    case Con{+x, +rest}:
      keep_link_pick(grammar, e, x, rest, G.ebnf_member_cases(e, x, rest, m), ok,
        later => keep_link_member(rest, grammar, e, later, ok))

law all_in_links:
  for xs: +List<Spec.Bsr>
  for +ys: +List<Spec.Bsr>
  for +grammar: +List<Spec.Production>
  for inY: {Spec.allIn(xs, ys) == True{} : Bool}
  for links: {allLink(xs, grammar) == True{} : Bool}
  {Spec.allIn(xs, Prune.keepLinks(ys, grammar)) == True{} : Bool}

def all_in_links(xs, ys, grammar, inY, links):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +bothY = inY
      +bothL = links
      Lemma.and_true_intro(Spec.bsrMember(x, Prune.keepLinks(ys, grammar)), Spec.allIn(rest, Prune.keepLinks(ys, grammar)),
        keep_link_member(ys, grammar, x, Lemma.and_true_left(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), bothY), Lemma.and_true_left(Prune.linkOk(grammar, x), allLink(rest, grammar), bothL)),
        all_in_links(rest, ys, grammar, Lemma.and_true_right_side(Spec.bsrMember(x, ys), Spec.allIn(rest, ys), bothY), Lemma.and_true_right_side(Prune.linkOk(grammar, x), allLink(rest, grammar), bothL)))

# The rule keeps every step of every parse tree that its input has.
law rule_found:
  for found: Maybe<&2, +List<Spec.Bsr>>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for every: FoundSteps(found, grammar, start, input)
  FoundSteps(Prune.roundRule(found, grammar), grammar, start, input)

def rule_found(found, grammar, start, input, every):
  match found:
    case Some{+ys}:
      +tree => +fitting => spelled => all_in_links(Spec.steps(tree, 0n), ys, grammar, every(tree, fitting, spelled), tree_links(grammar, start, tree, fitting))
    case None{}:
      Unit{}

# THE RESULT: after the round rule, the checked parser's steps still have every step of
# every parse tree.
law rounds_found:
  for +fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  FoundSteps(Prune.roundRule(Check.checkedSteps(fuel, grammar, start, input), grammar), grammar, start, input)

def rounds_found(fuel, grammar, start, input):
  rule_found(Check.checkedSteps(fuel, grammar, start, input), grammar, start, input, checked_found(fuel, grammar, start, input))
