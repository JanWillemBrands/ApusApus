import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./LEMMAS.bend as Lemma
import ./FITS.bend as Fits

# Proofs of the rewriting laws in LAWS.bend.
#
# A forest fits a sequence of items one tree per item, so it splits and joins like the
# sequence: the head tree fits the head item and the rest fits the rest (FITS.bend),
# and a forest for a concatenation of items is a concatenation of forests (fits_split,
# fits_append). Each law then rearranges the trees for the bracket it is about. A
# round or a taken [ ] that reads nothing is dropped where a law would make it
# removable (SPEC.bend, roundsOk): its leaves are empty, so the input is the same.

# ---- Leaves ----

law nat_append_assoc:
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for +zs: +List<Nat>
  {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : +List<Nat>}

def nat_append_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(+List<Nat>, +List<Nat>, v => x <> v, List.append(&2, Nat, List.append(&2, Nat, rest, ys), zs), List.append(&2, Nat, rest, List.append(&2, Nat, ys, zs)), nat_append_assoc(rest, ys, zs))

law leaves_cons:
  for t: Spec.Tree
  for +ts: +List<Spec.Tree>
  {Spec.leaves(t <> ts) == List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)) : +List<Nat>}

def leaves_cons(t, ts):
  match t:
    case Spec.Leaf{kind}:
      {==}
    case Spec.Node{q, +ch}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Pick{a, +ch}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(ch), List.append(&2, Nat, Spec.leaves(ch), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(ch), []), Spec.leaves(ch), Lemma.append_nil_right(Spec.leaves(ch))))
    case Spec.Skip{}:
      {==}
    case Spec.Loop{+rs}:
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves(rs), List.append(&2, Nat, Spec.leaves(rs), []), Equal.sym(+List<Nat>, List.append(&2, Nat, Spec.leaves(rs), []), Spec.leaves(rs), Lemma.append_nil_right(Spec.leaves(rs))))

law leaves_append:
  for f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  {Spec.leaves(List.append(&2, Spec.Tree, f1, f2)) == List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)) : +List<Nat>}

def leaves_append(f1, f2):
  match f1:
    case Nil{}:
      {==}
    case Con{+t, +ts}:
      +lt = Spec.leaves([t])
      Equal.trans(+List<Nat>, Spec.leaves(t <> List.append(&2, Spec.Tree, ts, f2)), List.append(&2, Nat, lt, Spec.leaves(List.append(&2, Spec.Tree, ts, f2))), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(f2)),
        leaves_cons(t, List.append(&2, Spec.Tree, ts, f2)),
        Equal.trans(+List<Nat>, List.append(&2, Nat, lt, Spec.leaves(List.append(&2, Spec.Tree, ts, f2))), List.append(&2, Nat, lt, List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2))), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(f2)),
          Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, lt, v), Spec.leaves(List.append(&2, Spec.Tree, ts, f2)), List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2)), leaves_append(ts, f2)),
          Equal.trans(+List<Nat>, List.append(&2, Nat, lt, List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2))), List.append(&2, Nat, List.append(&2, Nat, lt, Spec.leaves(ts)), Spec.leaves(f2)), List.append(&2, Nat, Spec.leaves(t <> ts), Spec.leaves(f2)),
            Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, lt, Spec.leaves(ts)), Spec.leaves(f2)), List.append(&2, Nat, lt, List.append(&2, Nat, Spec.leaves(ts), Spec.leaves(f2))), nat_append_assoc(lt, Spec.leaves(ts), Spec.leaves(f2))),
            Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(f2)), List.append(&2, Nat, lt, Spec.leaves(ts)), Spec.leaves(t <> ts), Equal.sym(+List<Nat>, Spec.leaves(t <> ts), List.append(&2, Nat, lt, Spec.leaves(ts)), leaves_cons(t, ts))))))

# ---- Concatenations ----

# A forest for xs then a forest for ys is a forest for xs ++ ys.
law fits_append:
  for f1: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for xs: +List<Spec.Item>
  for +ys: +List<Spec.Item>
  for e1: {Spec.fits(f1, grammar, xs) == True{} : Bool}
  for +e2: {Spec.fits(f2, grammar, ys) == True{} : Bool}
  {Spec.fits(List.append(&2, Spec.Tree, f1, f2), grammar, List.append(&2, Spec.Item, xs, ys)) == True{} : Bool}

def fits_append(f1, f2, grammar, xs, ys, e1, e2):
  match f1 xs:
    case Nil{} Nil{}:
      e2
    case Nil{} Con{it, rest}:
      Empty.absurd({Spec.fits(f2, grammar, it <> List.append(&2, Spec.Item, rest, ys)) == True{} : Bool}, Lemma.false_is_not_true(e1))
    case Con{t, ts} Nil{}:
      Empty.absurd({Spec.fits(t <> List.append(&2, Spec.Tree, ts, f2), grammar, ys) == True{} : Bool}, Fits.fits_cons_nil(t, ts, grammar, e1))
    case Con{+t, +ts} Con{+it, +rest}:
      +both = e1
      Fits.fits_join(t, List.append(&2, Spec.Tree, ts, f2), grammar, it, List.append(&2, Spec.Item, rest, ys),
        Fits.fits_head(t, ts, grammar, it, rest, both),
        fits_append(ts, f2, grammar, rest, ys, Fits.fits_tail(t, ts, grammar, it, rest, both), e2))

def Split(+grammar: +List<Spec.Production>, +forest: +List<Spec.Tree>, +xs: +List<Spec.Item>, +ys: +List<Spec.Item>) -> Type:
  &f1: +List<Spec.Tree> -> &f2: +List<Spec.Tree> -> {forest == List.append(&2, Spec.Tree, f1, f2) : +List<Spec.Tree>} & {Spec.fits(f1, grammar, xs) == True{} : Bool} & {Spec.fits(f2, grammar, ys) == True{} : Bool}

law split_cons:
  for +grammar: +List<Spec.Production>
  for +t: Spec.Tree
  for -ts: +List<Spec.Tree>
  for +it: Spec.Item
  for +rest: +List<Spec.Item>
  for -ys: +List<Spec.Item>
  for +head: {Spec.fits([t], grammar, [it]) == True{} : Bool}
  for later: Split(grammar, ts, rest, ys)
  Split(grammar, t <> ts, it <> rest, ys)

def split_cons(grammar, t, ts, it, rest, ys, head, later):
  match later:
    case (f10, (f2, (eq, (e1, e2)))):
      +f1 = {f10 : +List<Spec.Tree>}
      (t <> f1, (f2, (Equal.cong(+List<Spec.Tree>, +List<Spec.Tree>, v => t <> v, ts, List.append(&2, Spec.Tree, f1, f2), eq), (Fits.fits_join(t, f1, grammar, it, rest, head, e1), e2))))

# A forest for xs ++ ys splits into a forest for xs and one for ys.
law fits_split:
  for forest: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for xs: +List<Spec.Item>
  for +ys: +List<Spec.Item>
  for e: {Spec.fits(forest, grammar, List.append(&2, Spec.Item, xs, ys)) == True{} : Bool}
  Split(grammar, forest, xs, ys)

def fits_split(forest, grammar, xs, ys, e):
  match forest xs:
    case _ Nil{}:
      ([], (forest, ({==}, ({==}, e))))
    case Nil{} Con{it, rest}:
      Empty.absurd(Split(grammar, [], it <> rest, ys), Lemma.false_is_not_true(e))
    case Con{+t, +ts} Con{+it, +rest}:
      +both = e
      split_cons(grammar, t, ts, it, rest, ys,
        Fits.fits_head(t, ts, grammar, it, List.append(&2, Spec.Item, rest, ys), both),
        fits_split(ts, grammar, rest, ys, Fits.fits_tail(t, ts, grammar, it, List.append(&2, Spec.Item, rest, ys), both)))

# ---- Rounds that read nothing ----

law empty_of_not:
  for xs: +List<Nat>
  for h: {Bool.not(List.is_empty(&2, Nat, xs)) == False{} : Bool}
  {xs == [] : +List<Nat>}

def empty_of_not(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      Empty.absurd({x <> rest == [] : +List<Nat>}, Lemma.true_is_not_false(h))

# A tree that reads nothing can be dropped from in front of the others.
law leaves_drop:
  for +t: Spec.Tree
  for +ts: +List<Spec.Tree>
  for empty: {Spec.consumes(t) == False{} : Bool}
  {Spec.leaves(t <> ts) == Spec.leaves(ts) : +List<Nat>}

def leaves_drop(t, ts, empty):
  Equal.trans(+List<Nat>, Spec.leaves(t <> ts), List.append(&2, Nat, Spec.leaves([t]), Spec.leaves(ts)), Spec.leaves(ts),
    leaves_cons(t, ts),
    Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, Spec.leaves(ts)), Spec.leaves([t]), [], empty_of_not(Spec.leaves([t]), empty)))

# The rounds of a { } read input.
law closure_all:
  for rs: +List<Spec.Tree>
  for h: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  {Spec.allConsume(rs) == True{} : Bool}

def closure_all(rs, h):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rr}:
      Lemma.or_false_right(Spec.allConsume(r <> rr), h)

law closure_ok:
  for rs: +List<Spec.Tree>
  for ac: {Spec.allConsume(rs) == True{} : Bool}
  {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}

def closure_ok(rs, ac):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rr}:
      Lemma.or_true_left_intro(Spec.allConsume(r <> rr), False{}, ac)

law closure_tail:
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for h: {Spec.roundsOk(Spec.Closure{}, r <> rs) == True{} : Bool}
  {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}

def closure_tail(r, rs, h):
  closure_ok(rs, Lemma.and_true_right_side(Spec.consumes(r), Spec.allConsume(rs), closure_all(r <> rs, h)))

law single_rest:
  for rs: +List<Spec.Tree>
  for one: {Nat.is_eq(1n+List.length(&2, Spec.Tree, rs), 1n) == True{} : Bool}
  {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}

def single_rest(rs, one):
  match rs:
    case Nil{}:
      {==}
    case Con{x, xs}:
      Empty.absurd({Spec.roundsOk(Spec.Closure{}, x <> xs) == True{} : Bool}, Lemma.false_is_not_true(one))

law positive_tail_pick:
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for cases: Either<{Spec.allConsume(r <> rs) == True{} : Bool}, {Nat.is_eq(1n+List.length(&2, Spec.Tree, rs), 1n) == True{} : Bool}>
  {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}

def positive_tail_pick(r, rs, cases):
  match cases:
    case Inl{allC}:
      closure_ok(rs, Lemma.and_true_right_side(Spec.consumes(r), Spec.allConsume(rs), allC))
    case Inr{one}:
      single_rest(rs, one)

# After the first round of a < >, the rest are allowed rounds of a { }.
law positive_tail:
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for h: {Spec.roundsOk(Spec.Positive{}, r <> rs) == True{} : Bool}
  {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}

def positive_tail(r, rs, h):
  +n = List.length(&2, Spec.Tree, r <> rs)
  +more = Lemma.and_true_right_side(Bool.not(Nat.is_lt(n, 1n)), Bool.or(Spec.allConsume(r <> rs), Nat.is_eq(n, 1n)), h)
  positive_tail_pick(r, rs, Lemma.or_true_cases(Spec.allConsume(r <> rs), Nat.is_eq(n, 1n), more))

# ---- Moving a round in and out of a loop ----

law leaves_unloop:
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  {Spec.leaves(r <> Spec.Loop{rs} <> ts) == Spec.leaves(Spec.Loop{r <> rs} <> ts) : +List<Nat>}

def leaves_unloop(r, rs, ts):
  +lr = Spec.leaves([r])
  +lrs = Spec.leaves(rs)
  +lts = Spec.leaves(ts)
  Equal.trans(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), List.append(&2, Nat, lr, List.append(&2, Nat, lrs, lts)), List.append(&2, Nat, Spec.leaves(r <> rs), lts),
    leaves_cons(r, Spec.Loop{rs} <> ts),
    Equal.trans(+List<Nat>, List.append(&2, Nat, lr, List.append(&2, Nat, lrs, lts)), List.append(&2, Nat, List.append(&2, Nat, lr, lrs), lts), List.append(&2, Nat, Spec.leaves(r <> rs), lts),
      Equal.sym(+List<Nat>, List.append(&2, Nat, List.append(&2, Nat, lr, lrs), lts), List.append(&2, Nat, lr, List.append(&2, Nat, lrs, lts)), nat_append_assoc(lr, lrs, lts)),
      Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, lts), List.append(&2, Nat, lr, lrs), Spec.leaves(r <> rs), Equal.sym(+List<Nat>, Spec.leaves(r <> rs), List.append(&2, Nat, lr, lrs), leaves_cons(r, rs)))))

# A loop with a first round r is r next to a loop without it.
law unloop:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for rounds: {Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for okRs: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  for later: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for l: {Spec.leaves(Spec.Loop{r <> rs} <> ts) == w : +List<Nat>}
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)

def unloop(grammar, alts, rest, w, r, rs, ts, rounds, okRs, later, l):
  +g = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
  +more = Spec.times(List.length(&2, Spec.Tree, rs), g)
  +both = rounds
  +fitsRest = Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, more)), Spec.fits(ts, grammar, rest),
    Lemma.and_true_intro(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, more), okRs, Fits.fits_tail(r, rs, grammar, g, more, both)), later)
  (r <> Spec.Loop{rs} <> ts, (Fits.fits_join(r, Spec.Loop{rs} <> ts, grammar, g, Spec.Brack{Spec.Closure{}, alts} <> rest, Fits.fits_head(r, rs, grammar, g, more, both), fitsRest),
    Equal.trans(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), Spec.leaves(Spec.Loop{r <> rs} <> ts), w, leaves_unloop(r, rs, ts), l)))

# A round next to a loop: the round, and the loop's allowed rounds.
def Reloop(+grammar: +List<Spec.Production>, +alts: +List<+List<Spec.Item>>, +rest: +List<Spec.Item>, +w: +List<Nat>) -> Type:
  &r: Spec.Tree -> &rs: +List<Spec.Tree> -> &ts: +List<Spec.Tree> ->
    {Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool} & {Spec.fits(ts, grammar, rest) == True{} : Bool} & {Spec.leaves(r <> Spec.Loop{rs} <> ts) == w : +List<Nat>}

law reloop:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for forest: +List<Spec.Tree>
  for f: {Spec.fits(forest, grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest) == True{} : Bool}
  for l: {Spec.leaves(forest) == w : +List<Nat>}
  Reloop(grammar, alts, rest, w)

def reloop(grammar, alts, rest, w, forest, f, l):
  match forest:
    case Nil{}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(f))
    case Con{+r, Nil{}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(Fits.fits_tail(r, [], grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Leaf{k}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(Fits.fits_tail(r, Spec.Leaf{k} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Node{+q, +ch}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(Fits.fits_tail(r, Spec.Node{q, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Pick{+a, +ch}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(Fits.fits_tail(r, Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Skip{}, +ts}}:
      Empty.absurd(Reloop(grammar, alts, rest, w), Lemma.false_is_not_true(Fits.fits_tail(r, Spec.Skip{} <> ts, grammar, Spec.Brack{Spec.Group{}, alts}, Spec.Brack{Spec.Closure{}, alts} <> rest, f)))
    case Con{+r, Con{Spec.Loop{+rs}, +ts}}:
      +g = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +more = Spec.times(List.length(&2, Spec.Tree, rs), g)
      +both = f
      +tl = Fits.fits_tail(r, Spec.Loop{rs} <> ts, grammar, g, Spec.Brack{Spec.Closure{}, alts} <> rest, both)
      +x = Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, more))
      +hx = Lemma.and_true_left(x, Spec.fits(ts, grammar, rest), tl)
      rounds = Fits.fits_join(r, rs, grammar, g, more, Fits.fits_head(r, Spec.Loop{rs} <> ts, grammar, g, Spec.Brack{Spec.Closure{}, alts} <> rest, both), Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, more), hx))
      (r, (rs, (ts, (rounds, (Lemma.and_true_left(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, more), hx), (Lemma.and_true_right_side(x, Spec.fits(ts, grammar, rest), tl), l))))))

# ======== THE REWRITING LAWS ========

def Laws.empty_derives(grammar, w, d):
  match d:
    case (Nil{}, (f, l)):
      Equal.sym(+List<Nat>, [], w, l)
    case (Con{t, ts}, (f, l)):
      Empty.absurd({w == [] : +List<Nat>}, Fits.fits_cons_nil(t, ts, grammar, f))

def Laws.terminal_unfold(grammar, k, rest, w, d):
  match d:
    case (Nil{}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{+kind}, +ts}, (f, l)):
      +both = f
      kEq = Lemma.nat_eq_sound(kind, k, Lemma.and_true_left(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), both))
      wEq = Equal.trans(+List<Nat>, w, kind <> Spec.leaves(ts), k <> Spec.leaves(ts), Equal.sym(+List<Nat>, kind <> Spec.leaves(ts), w, l), Equal.cong(Nat, +List<Nat>, x => x <> Spec.leaves(ts), kind, k, kEq))
      (Spec.leaves(ts), (wEq, (ts, (Lemma.and_true_right_side(Nat.is_eq(kind, k), Spec.fits(ts, grammar, rest), both), {==}))))
    case (Con{Spec.Node{q, ch}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a, ch}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{rs}, ts}, (f, l)):
      Empty.absurd(Sigma<&1, &1, +List<Nat>, w2 => {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)>, Lemma.false_is_not_true(f))

def Laws.nonterminal_unfold(grammar, a, rest, w, d):
  match d:
    case (Con{Spec.Node{+p, +ch}, +ts}, (f, l)):
      +h = Bool.and(Spec.lhsIs(grammar, p, a), Spec.fits(ch, grammar, Spec.rhsOf(grammar, p)))
      +both = f
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both)
      lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, p, a), Spec.fits(ch, grammar, Spec.rhsOf(grammar, p)), hOk)
      fch = Lemma.and_true_right_side(Spec.lhsIs(grammar, p, a), Spec.fits(ch, grammar, Spec.rhsOf(grammar, p)), hOk)
      fts = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both)
      (p, (lhsOk, (List.append(&2, Spec.Tree, ch, ts), (fits_append(ch, ts, grammar, Spec.rhsOf(grammar, p), rest, fch, fts),
        Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, ch, ts)), List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(ts)), w, leaves_append(ch, ts), l)))))
    case (Nil{}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a0, c0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, p => {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)>, Lemma.false_is_not_true(f))

def Laws.group_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Pick{+a, +ch}, +ts}, (f, l)):
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +both = f
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both)
      isA = Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      fch = Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk)
      fts = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both)
      (a, (isA, (List.append(&2, Spec.Tree, ch, ts), (fits_append(ch, ts, grammar, Spec.altOf(alts, a), rest, fch, fts),
        Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, ch, ts)), List.append(&2, Nat, Spec.leaves(ch), Spec.leaves(ts)), w, leaves_append(ch, ts), l)))))
    case (Nil{}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Sigma<&1, &1, Nat, a => {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)>, Lemma.false_is_not_true(f))

law nonterminal_join:
  for +grammar: +List<Spec.Production>
  for +a: Nat
  for +p: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +forest: +List<Spec.Tree>
  for lhsOk: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  for l: {Spec.leaves(forest) == w : +List<Nat>}
  for sp: Split(grammar, forest, Spec.rhsOf(grammar, p), rest)
  Spec.Derives(grammar, Spec.Sym{Spec.Nonterminal{a}} <> rest, w)

def nonterminal_join(grammar, a, p, rest, w, forest, lhsOk, l, sp):
  match sp:
    case (f10, (f20, (eq, (e1, e2)))):
      +f1 = {f10 : +List<Spec.Tree>}
      +f2 = {f20 : +List<Spec.Tree>}
      +lEq = Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), Spec.leaves(forest), w,
        Equal.cong(+List<Spec.Tree>, +List<Nat>, x => Spec.leaves(x), List.append(&2, Spec.Tree, f1, f2), forest, Equal.sym(+List<Spec.Tree>, forest, List.append(&2, Spec.Tree, f1, f2), eq)), l)
      (Spec.Node{p, f1} <> f2, (Lemma.and_true_intro(Bool.and(Spec.lhsIs(grammar, p, a), Spec.fits(f1, grammar, Spec.rhsOf(grammar, p))), Spec.fits(f2, grammar, rest), Lemma.and_true_intro(Spec.lhsIs(grammar, p, a), Spec.fits(f1, grammar, Spec.rhsOf(grammar, p)), lhsOk, e1), e2),
        Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), w, Equal.sym(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), leaves_append(f1, f2)), lEq)))

def Laws.nonterminal_fold(grammar, a, p, rest, w, lhsOk, d):
  match d:
    case (forest0, (f, l)):
      +forest = {forest0 : +List<Spec.Tree>}
      nonterminal_join(grammar, a, p, rest, w, forest, lhsOk, l, fits_split(forest, grammar, Spec.rhsOf(grammar, p), rest, f))

law group_join:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +forest: +List<Spec.Tree>
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for l: {Spec.leaves(forest) == w : +List<Nat>}
  for sp: Split(grammar, forest, Spec.altOf(alts, a), rest)
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)

def group_join(grammar, alts, a, rest, w, forest, isA, l, sp):
  match sp:
    case (f10, (f20, (eq, (e1, e2)))):
      +f1 = {f10 : +List<Spec.Tree>}
      +f2 = {f20 : +List<Spec.Tree>}
      +lEq = Equal.trans(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), Spec.leaves(forest), w,
        Equal.cong(+List<Spec.Tree>, +List<Nat>, x => Spec.leaves(x), List.append(&2, Spec.Tree, f1, f2), forest, Equal.sym(+List<Spec.Tree>, forest, List.append(&2, Spec.Tree, f1, f2), eq)), l)
      (Spec.Pick{a, f1} <> f2, (Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(f1, grammar, Spec.altOf(alts, a))), Spec.fits(f2, grammar, rest), Lemma.and_true_intro(Spec.isAlt(alts, a), Spec.fits(f1, grammar, Spec.altOf(alts, a)), isA, e1), e2),
        Equal.trans(+List<Nat>, List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), w, Equal.sym(+List<Nat>, Spec.leaves(List.append(&2, Spec.Tree, f1, f2)), List.append(&2, Nat, Spec.leaves(f1), Spec.leaves(f2)), leaves_append(f1, f2)), lEq)))

def Laws.group_fold(grammar, alts, a, rest, w, isA, d):
  match d:
    case (forest0, (f, l)):
      +forest = {forest0 : +List<Spec.Tree>}
      group_join(grammar, alts, a, rest, w, forest, isA, l, fits_split(forest, grammar, Spec.altOf(alts, a), rest, f))

def Laws.optional_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Skip{}, ts}, (f, l)):
      Inl{(ts, (f, l))}
    case (Con{Spec.Pick{+a, +ch}, +ts}, (f, l)):
      +h0 = Bool.and(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a))
      +h1 = Bool.and(h0, Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +both = f
      +hk = Lemma.and_true_left(h1, Spec.fits(ts, grammar, rest), both)
      +hr = Lemma.and_true_left(h0, Spec.fits(ch, grammar, Spec.altOf(alts, a)), hk)
      Inr{(Spec.Pick{a, ch} <> ts, (Lemma.and_true_intro(Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest),
        Lemma.and_true_intro(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_right_side(Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}]), Spec.isAlt(alts, a), hr), Lemma.and_true_right_side(h0, Spec.fits(ch, grammar, Spec.altOf(alts, a)), hk)),
        Lemma.and_true_right_side(h1, Spec.fits(ts, grammar, rest), both)), l))}
    case (Nil{}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))

# A taken ( ): taken in the [ ] when it reads input, else skipped.
law optional_pick:
  for c: Bool
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +cEq: {Spec.consumes(Spec.Pick{a, ch}) == c : Bool}
  for +f: {Spec.fits(Spec.Pick{a, ch} <> ts, grammar, Spec.Brack{Spec.Group{}, alts} <> rest) == True{} : Bool}
  for +l: {Spec.leaves(Spec.Pick{a, ch} <> ts) == w : +List<Nat>}
  Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w)

def optional_pick(c, grammar, alts, rest, w, a, ch, ts, cEq, f, l):
  match c:
    case True{}:
      +hg = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +hk = Lemma.and_true_left(hg, Spec.fits(ts, grammar, rest), f)
      +read = Spec.consumes(Spec.Pick{a, ch})
      +rOk = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
      +ok = Lemma.or_true_left_intro(Bool.and(read, True{}), False{}, Lemma.and_true_intro(read, True{}, cEq, {==}))
      (Spec.Pick{a, ch} <> ts, (Lemma.and_true_intro(Bool.and(Bool.and(rOk, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a))), Spec.fits(ts, grammar, rest),
        Lemma.and_true_intro(Bool.and(rOk, Spec.isAlt(alts, a)), Spec.fits(ch, grammar, Spec.altOf(alts, a)), Lemma.and_true_intro(rOk, Spec.isAlt(alts, a), ok, Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hk)), Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hk)),
        Lemma.and_true_right_side(hg, Spec.fits(ts, grammar, rest), f)), l))
    case False{}:
      +hg = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      (Spec.Skip{} <> ts, (Lemma.and_true_right_side(hg, Spec.fits(ts, grammar, rest), f),
        Equal.trans(+List<Nat>, Spec.leaves(ts), Spec.leaves(Spec.Pick{a, ch} <> ts), w, Equal.sym(+List<Nat>, Spec.leaves(Spec.Pick{a, ch} <> ts), Spec.leaves(ts), leaves_drop(Spec.Pick{a, ch}, ts, cEq)), l)))

law optional_take:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w)

def optional_take(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Pick{+a, +ch}, +ts}, (f, l)):
      optional_pick(Spec.consumes(Spec.Pick{a, ch}), grammar, alts, rest, w, a, ch, ts, {==}, f, l)
    case (Nil{}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w), Lemma.false_is_not_true(f))

def Laws.optional_fold(grammar, alts, rest, w, d):
  match d:
    case Inl{skip}:
      match skip:
        case (forest, (f, l)):
          (Spec.Skip{} <> forest, (f, l))
    case Inr{take}:
      optional_take(grammar, alts, rest, w, take)

def Laws.closure_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Loop{Nil{}}, ts}, (f, l)):
      Inl{(ts, (f, l))}
    case (Con{Spec.Loop{Con{+r, +rs}}, +ts}, (f, l)):
      +tm = Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})
      +h = Bool.and(Spec.roundsOk(Spec.Closure{}, r <> rs), Spec.fits(r <> rs, grammar, tm))
      +both = f
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both)
      Inr{unloop(grammar, alts, rest, w, r, rs, ts, Lemma.and_true_right_side(Spec.roundsOk(Spec.Closure{}, r <> rs), Spec.fits(r <> rs, grammar, tm), hOk),
        closure_tail(r, rs, Lemma.and_true_left(Spec.roundsOk(Spec.Closure{}, r <> rs), Spec.fits(r <> rs, grammar, tm), hOk)), Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both), l)}
    case (Nil{}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a0, c0}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>, Lemma.false_is_not_true(f))

def Laws.positive_unfold(grammar, alts, rest, w, d):
  match d:
    case (Con{Spec.Loop{Nil{}}, ts}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{Con{+r, +rs}}, +ts}, (f, l)):
      +tm = Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})
      +h = Bool.and(Spec.roundsOk(Spec.Positive{}, r <> rs), Spec.fits(r <> rs, grammar, tm))
      +both = f
      +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), both)
      unloop(grammar, alts, rest, w, r, rs, ts, Lemma.and_true_right_side(Spec.roundsOk(Spec.Positive{}, r <> rs), Spec.fits(r <> rs, grammar, tm), hOk),
        positive_tail(r, rs, Lemma.and_true_left(Spec.roundsOk(Spec.Positive{}, r <> rs), Spec.fits(r <> rs, grammar, tm), hOk)), Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), both), l)
    case (Nil{}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Skip{}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w), Lemma.false_is_not_true(f))

# A round next to a { }: joined to it when it reads input, else dropped.
law closure_pick:
  for c: Bool
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +cEq: {Spec.consumes(r) == c : Bool}
  for +rounds: {Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +okRs: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  for +later: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +l: {Spec.leaves(r <> Spec.Loop{rs} <> ts) == w : +List<Nat>}
  Spec.Derives(grammar, Spec.Brack{Spec.Closure{}, alts} <> rest, w)

def closure_pick(c, grammar, alts, rest, w, r, rs, ts, cEq, rounds, okRs, later, l):
  match c:
    case True{}:
      +g = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +tmAll = Spec.times(List.length(&2, Spec.Tree, r <> rs), g)
      +ok = closure_ok(r <> rs, Lemma.and_true_intro(Spec.consumes(r), Spec.allConsume(rs), cEq, closure_all(rs, okRs)))
      (Spec.Loop{r <> rs} <> ts, (Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Closure{}, r <> rs), Spec.fits(r <> rs, grammar, tmAll)), Spec.fits(ts, grammar, rest), Lemma.and_true_intro(Spec.roundsOk(Spec.Closure{}, r <> rs), Spec.fits(r <> rs, grammar, tmAll), ok, rounds), later),
        Equal.trans(+List<Nat>, Spec.leaves(Spec.Loop{r <> rs} <> ts), Spec.leaves(r <> Spec.Loop{rs} <> ts), w, Equal.sym(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), Spec.leaves(Spec.Loop{r <> rs} <> ts), leaves_unloop(r, rs, ts)), l)))
    case False{}:
      +g = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +tm = Spec.times(List.length(&2, Spec.Tree, rs), g)
      (Spec.Loop{rs} <> ts, (Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tm)), Spec.fits(ts, grammar, rest), Lemma.and_true_intro(Spec.roundsOk(Spec.Closure{}, rs), Spec.fits(rs, grammar, tm), okRs, Fits.fits_tail(r, rs, grammar, g, tm, rounds)), later),
        Equal.trans(+List<Nat>, Spec.leaves(Spec.Loop{rs} <> ts), Spec.leaves(r <> Spec.Loop{rs} <> ts), w, Equal.sym(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), Spec.leaves(Spec.Loop{rs} <> ts), leaves_drop(r, Spec.Loop{rs} <> ts, cEq)), l)))

law closure_more:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for re: Reloop(grammar, alts, rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Closure{}, alts} <> rest, w)

def closure_more(grammar, alts, rest, w, re):
  match re:
    case (r0, (rs0, (ts0, (rounds, (okRs, (later, l)))))):
      +r = {r0 : Spec.Tree}
      +rs = {rs0 : +List<Spec.Tree>}
      +ts = {ts0 : +List<Spec.Tree>}
      closure_pick(Spec.consumes(r), grammar, alts, rest, w, r, rs, ts, {==}, rounds, okRs, later, l)

law not_lt_one:
  for n: Nat
  {Bool.not(Nat.is_lt(1n+n, 1n)) == True{} : Bool}

def not_lt_one(n):
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

# A < > after a first round that reads nothing: that round alone, or the others.
law positive_empty:
  for rs: +List<Spec.Tree>
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +r: Spec.Tree
  for +ts: +List<Spec.Tree>
  for +cEq: {Spec.consumes(r) == False{} : Bool}
  for +rounds: {Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +okRs: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  for +later: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +l: {Spec.leaves(r <> Spec.Loop{rs} <> ts) == w : +List<Nat>}
  Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)

def positive_empty(rs, grammar, alts, rest, w, r, ts, cEq, rounds, okRs, later, l):
  match rs:
    case Nil{}:
      +tm = Spec.times(1n, Spec.Brack{Spec.Group{}, alts})
      +ok = Lemma.or_true_right_intro(Spec.allConsume([r]), True{}, {==})
      (Spec.Loop{[r]} <> ts, (Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Positive{}, [r]), Spec.fits([r], grammar, tm)), Spec.fits(ts, grammar, rest), Lemma.and_true_intro(Spec.roundsOk(Spec.Positive{}, [r]), Spec.fits([r], grammar, tm), ok, rounds), later),
        Equal.trans(+List<Nat>, Spec.leaves(Spec.Loop{[r]} <> ts), Spec.leaves(r <> Spec.Loop{[]} <> ts), w, Equal.sym(+List<Nat>, Spec.leaves(r <> Spec.Loop{[]} <> ts), Spec.leaves(Spec.Loop{[r]} <> ts), leaves_unloop(r, [], ts)), l)))
    case Con{+r2, +rs2}:
      +g = {Spec.Brack{Spec.Group{}, alts} : Spec.Item}
      +tm = Spec.times(List.length(&2, Spec.Tree, r2 <> rs2), g)
      +n = List.length(&2, Spec.Tree, rs2)
      +ok = Lemma.and_true_intro(Bool.not(Nat.is_lt(1n+n, 1n)), Bool.or(Spec.allConsume(r2 <> rs2), Nat.is_eq(1n+n, 1n)), not_lt_one(n),
        Lemma.or_true_left_intro(Spec.allConsume(r2 <> rs2), Nat.is_eq(1n+n, 1n), closure_all(r2 <> rs2, okRs)))
      (Spec.Loop{r2 <> rs2} <> ts, (Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Positive{}, r2 <> rs2), Spec.fits(r2 <> rs2, grammar, tm)), Spec.fits(ts, grammar, rest), Lemma.and_true_intro(Spec.roundsOk(Spec.Positive{}, r2 <> rs2), Spec.fits(r2 <> rs2, grammar, tm), ok, Fits.fits_tail(r, r2 <> rs2, grammar, g, tm, rounds)), later),
        Equal.trans(+List<Nat>, Spec.leaves(Spec.Loop{r2 <> rs2} <> ts), Spec.leaves(r <> Spec.Loop{r2 <> rs2} <> ts), w, Equal.sym(+List<Nat>, Spec.leaves(r <> Spec.Loop{r2 <> rs2} <> ts), Spec.leaves(Spec.Loop{r2 <> rs2} <> ts), leaves_drop(r, Spec.Loop{r2 <> rs2} <> ts, cEq)), l)))

law positive_pick:
  for c: Bool
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for +r: Spec.Tree
  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +cEq: {Spec.consumes(r) == c : Bool}
  for +rounds: {Spec.fits(r <> rs, grammar, Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
  for +okRs: {Spec.roundsOk(Spec.Closure{}, rs) == True{} : Bool}
  for +later: {Spec.fits(ts, grammar, rest) == True{} : Bool}
  for +l: {Spec.leaves(r <> Spec.Loop{rs} <> ts) == w : +List<Nat>}
  Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)

def positive_pick(c, grammar, alts, rest, w, r, rs, ts, cEq, rounds, okRs, later, l):
  match c:
    case True{}:
      +tmAll = Spec.times(List.length(&2, Spec.Tree, r <> rs), Spec.Brack{Spec.Group{}, alts})
      +n = List.length(&2, Spec.Tree, rs)
      +ok = Lemma.and_true_intro(Bool.not(Nat.is_lt(1n+n, 1n)), Bool.or(Spec.allConsume(r <> rs), Nat.is_eq(1n+n, 1n)), not_lt_one(n),
        Lemma.or_true_left_intro(Spec.allConsume(r <> rs), Nat.is_eq(1n+n, 1n), Lemma.and_true_intro(Spec.consumes(r), Spec.allConsume(rs), cEq, closure_all(rs, okRs))))
      (Spec.Loop{r <> rs} <> ts, (Lemma.and_true_intro(Bool.and(Spec.roundsOk(Spec.Positive{}, r <> rs), Spec.fits(r <> rs, grammar, tmAll)), Spec.fits(ts, grammar, rest), Lemma.and_true_intro(Spec.roundsOk(Spec.Positive{}, r <> rs), Spec.fits(r <> rs, grammar, tmAll), ok, rounds), later),
        Equal.trans(+List<Nat>, Spec.leaves(Spec.Loop{r <> rs} <> ts), Spec.leaves(r <> Spec.Loop{rs} <> ts), w, Equal.sym(+List<Nat>, Spec.leaves(r <> Spec.Loop{rs} <> ts), Spec.leaves(Spec.Loop{r <> rs} <> ts), leaves_unloop(r, rs, ts)), l)))
    case False{}:
      positive_empty(rs, grammar, alts, rest, w, r, ts, cEq, rounds, okRs, later, l)

law positive_more:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for re: Reloop(grammar, alts, rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)

def positive_more(grammar, alts, rest, w, re):
  match re:
    case (r0, (rs0, (ts0, (rounds, (okRs, (later, l)))))):
      +r = {r0 : Spec.Tree}
      +rs = {rs0 : +List<Spec.Tree>}
      +ts = {ts0 : +List<Spec.Tree>}
      positive_pick(Spec.consumes(r), grammar, alts, rest, w, r, rs, ts, {==}, rounds, okRs, later, l)

def Laws.closure_fold(grammar, alts, rest, w, d):
  match d:
    case Inl{none}:
      match none:
        case (forest, (f, l)):
          (Spec.Loop{[]} <> forest, (f, l))
    case Inr{more}:
      match more:
        case (forest, (f, l)):
          closure_more(grammar, alts, rest, w, reloop(grammar, alts, rest, w, forest, f, l))

def Laws.positive_fold(grammar, alts, rest, w, d):
  match d:
    case (forest, (f, l)):
      positive_more(grammar, alts, rest, w, reloop(grammar, alts, rest, w, forest, f, l))

def Laws.epsilon_unfold(grammar, rest, w, d):
  match d:
    case (Con{Spec.Skip{}, ts}, (f, l)):
      (ts, (f, l))
    case (Nil{}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Leaf{k0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Node{q0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Pick{a0, c0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, rest, w), Lemma.false_is_not_true(f))
    case (Con{Spec.Loop{r0}, ts0}, (f, l)):
      Empty.absurd(Spec.Derives(grammar, rest, w), Lemma.false_is_not_true(f))

def Laws.epsilon_fold(grammar, rest, w, d):
  match d:
    case (forest, (f, l)):
      (Spec.Skip{} <> forest, (f, l))
