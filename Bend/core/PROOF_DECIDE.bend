import Base
import ../LEMMAS.bend as Lemma
import ./CORE.bend as Core
import ./GLL.bend as Gll
import ./CLOSURE.bend as CL
import ./GUARD.bend as Guard
import ./PROOF_GLL.bend as G
import ./PROOF_PRUNE.bend as P
import ./PROOF_CLOSURE.bend as PCL
import ./PROOF_SPELL.bend as S

# THE GUARD ORACLE'S ANSWERS ARE RIGHT. "Does production q derive w?" Yes comes with a
# witness forest the oracle has checked with `reads`; No means the exact set of q's
# nonterminal over w has no completed step of q, while a forest of q over w would make a
# parse tree whose last step the exact set must hold. Everything else is built from these.

# ======== READS, FITS AND SPELLING ========

law reads_fits:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +r: {Core.reads(f, grammar, items, input, k) == True{} : Bool}
  {Core.fits(f, grammar, items) == True{} : Bool}

def reads_fits(f, items, grammar, input, k, r):
  match f items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+s, +rest}:
      Empty.absurd({Core.fits([], grammar, s <> rest) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({Core.fits(Core.Leaf{a} <> ts, grammar, []) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +more = {Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)) : Bool}
      Lemma.and_true_intro(Nat.is_eq(a, t), Core.fits(ts, grammar, rest), Lemma.and_true_left(Nat.is_eq(a, t), more, r),
        reads_fits(ts, rest, grammar, input, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), Lemma.and_true_right_side(Nat.is_eq(a, t), more, r))))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({Core.fits(Core.Leaf{a} <> ts, grammar, Core.Nonterminal{x, need} <> rest) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({Core.fits(Core.Node{q, ch} <> ts, grammar, []) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({Core.fits(Core.Node{q, ch} <> ts, grammar, Core.Terminal{t} <> rest) == True{} : Bool}, Lemma.false_is_not_true(r))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +head = {Bool.and(Core.lhsIs(grammar, q, x), Core.needOk(need, Core.width(Core.Node{q, ch}))) : Bool}
      +own = {Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k)) : Bool}
      +after = {Core.reads(ts, grammar, rest, input, Nat.add(k, Core.width(Core.Node{q, ch}))) : Bool}
      +left = Lemma.and_true_left(own, after, r)
      Lemma.and_true_intro(Bool.and(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q))), Core.fits(ts, grammar, rest),
        Lemma.and_true_intro(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q)), Lemma.and_true_left(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), left),
          reads_fits(ch, Core.rhsOf(grammar, q), grammar, input, k, Lemma.and_true_right_side(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), left))),
        reads_fits(ts, rest, grammar, input, Nat.add(k, Core.width(Core.Node{q, ch})), Lemma.and_true_right_side(own, after, r)))

law spells_left:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +h: {S.spells(List.append(&2, Nat, a, b), input, k) == True{} : Bool}
  {S.spells(a, input, k) == True{} : Bool}

def spells_left(a, b, input, k, h):
  match a:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), c), S.spells(rest, input, 1n+k),
        Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), c), S.spells(List.append(&2, Nat, rest, b), input, 1n+k), h),
        spells_left(rest, b, input, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), c), S.spells(List.append(&2, Nat, rest, b), input, 1n+k), h)))

law spells_at_zero:
  for +b: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +h: {S.spells(b, input, k) == True{} : Bool}
  {S.spells(b, input, Nat.add(k, 0n)) == True{} : Bool}

def spells_at_zero(b, input, k, h):
  %Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)) : {S.spells(b, input, _) == True{} : Bool}
  h

law spells_at_succ:
  for +b: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +la: Nat
  for +h: {S.spells(b, input, 1n+Nat.add(k, la)) == True{} : Bool}
  {S.spells(b, input, Nat.add(k, 1n+la)) == True{} : Bool}

def spells_at_succ(b, input, k, la, h):
  %Equal.sym(Nat, Nat.add(k, 1n+la), 1n+Nat.add(k, la), Lemma.add_succ_right(k, la)) : {S.spells(b, input, _) == True{} : Bool}
  h

law spells_right:
  for a: +List<Nat>
  for +b: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +h: {S.spells(List.append(&2, Nat, a, b), input, k) == True{} : Bool}
  {S.spells(b, input, Nat.add(k, List.length(&2, Nat, a))) == True{} : Bool}

def spells_right(a, b, input, k, h):
  match a:
    case Nil{}:
      spells_at_zero(b, input, k, h)
    case Con{+c, +rest}:
      spells_at_succ(b, input, k, List.length(&2, Nat, rest),
        spells_right(rest, b, input, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), c), S.spells(List.append(&2, Nat, rest, b), input, 1n+k), h)))

law width_back:
  for +ch: +List<Core.Tree>
  for +q2: Nat
  for +w: +List<Nat>
  for +input: +List<Nat>
  for +k: Nat
  for +h: {S.spells(w, input, Nat.add(k, List.length(&2, Nat, Core.leaves(ch)))) == True{} : Bool}
  {S.spells(w, input, Nat.add(k, Core.width(Core.Node{q2, ch}))) == True{} : Bool}

def width_back(ch, q2, w, input, k, h):
  %Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, Core.leaves(ch), [])), List.length(&2, Nat, Core.leaves(ch)), Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, Core.leaves(ch), []), Core.leaves(ch), Lemma.append_nil_right(Core.leaves(ch)))) : {S.spells(w, input, Nat.add(k, _)) == True{} : Bool}
  h

# A forest that fits and whose leaves are the input's tokens reads the input.
law fits_reads:
  for f: +List<Core.Tree>
  for items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +input: +List<Nat>
  for +k: Nat
  for +fit: {Core.fits(f, grammar, items) == True{} : Bool}
  for +sp: {S.spells(Core.leaves(f), input, k) == True{} : Bool}
  {Core.reads(f, grammar, items, input, k) == True{} : Bool}

def fits_reads(f, items, grammar, input, k, fit, sp):
  match f items:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+s, +rest}:
      Empty.absurd({Core.reads([], grammar, s <> rest, input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} Nil{}:
      Empty.absurd({Core.reads(Core.Leaf{a} <> ts, grammar, [], input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      Empty.absurd({Core.reads(Core.Leaf{a} <> ts, grammar, Core.Nonterminal{x, need} <> rest, input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Leaf{+a}, +ts} Con{Core.Terminal{+t}, +rest}:
      +tok = Lemma.and_true_left(Core.tokIs(Core.tokAt(input, k), a), S.spells(Core.leaves(ts), input, 1n+k), sp)
      +more = Lemma.and_true_right_side(Core.tokIs(Core.tokAt(input, k), a), S.spells(Core.leaves(ts), input, 1n+k), sp)
      Lemma.and_true_intro(Nat.is_eq(a, t), Bool.and(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k)),
        Lemma.and_true_left(Nat.is_eq(a, t), Core.fits(ts, grammar, rest), fit),
        Lemma.and_true_intro(Core.tokIs(Core.tokAt(input, k), a), Core.reads(ts, grammar, rest, input, 1n+k), tok,
          fits_reads(ts, rest, grammar, input, 1n+k, Lemma.and_true_right_side(Nat.is_eq(a, t), Core.fits(ts, grammar, rest), fit), more)))
    case Con{Core.Node{+q, +ch}, +ts} Nil{}:
      Empty.absurd({Core.reads(Core.Node{q, ch} <> ts, grammar, [], input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Terminal{+t}, +rest}:
      Empty.absurd({Core.reads(Core.Node{q, ch} <> ts, grammar, Core.Terminal{t} <> rest, input, k) == True{} : Bool}, Lemma.false_is_not_true(fit))
    case Con{Core.Node{+q, +ch}, +ts} Con{Core.Nonterminal{+x, +need}, +rest}:
      +far = {Nat.add(k, Core.width(Core.Node{q, ch})) : Nat}
      +head = {Bool.and(Core.lhsIs(grammar, q, x), Core.needOk(need, Core.width(Core.Node{q, ch}))) : Bool}
      +ownF = {Bool.and(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q))) : Bool}
      +leftF = Lemma.and_true_left(ownF, Core.fits(ts, grammar, rest), fit)
      +hd = Lemma.and_true_left(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q)), leftF)
      +fc = Lemma.and_true_right_side(head, Core.fits(ch, grammar, Core.rhsOf(grammar, q)), leftF)
      +ft = Lemma.and_true_right_side(ownF, Core.fits(ts, grammar, rest), fit)
      +sc = spells_left(Core.leaves(ch), Core.leaves(ts), input, k, sp)
      +st = width_back(ch, q, Core.leaves(ts), input, k, spells_right(Core.leaves(ch), Core.leaves(ts), input, k, sp))
      Lemma.and_true_intro(Bool.and(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k)), Core.reads(ts, grammar, rest, input, far),
        Lemma.and_true_intro(head, Core.reads(ch, grammar, Core.rhsOf(grammar, q), input, k), hd, fits_reads(ch, Core.rhsOf(grammar, q), grammar, input, k, fc, sc)),
        fits_reads(ts, rest, grammar, input, far, ft, st))

law spells_unshift:
  for w: +List<Nat>
  for +x: Nat
  for +xs: +List<Nat>
  for +k: Nat
  for +h: {S.spells(w, xs, k) == True{} : Bool}
  {S.spells(w, x <> xs, 1n+k) == True{} : Bool}

def spells_unshift(w, x, xs, k, h):
  match w:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      Lemma.and_true_intro(Core.tokIs(Core.tokAt(xs, k), c), S.spells(rest, x <> xs, 2n+k),
        Lemma.and_true_left(Core.tokIs(Core.tokAt(xs, k), c), S.spells(rest, xs, 1n+k), h),
        spells_unshift(rest, x, xs, 1n+k, Lemma.and_true_right_side(Core.tokIs(Core.tokAt(xs, k), c), S.spells(rest, xs, 1n+k), h)))

law spells_self:
  for w: +List<Nat>
  {S.spells(w, w, 0n) == True{} : Bool}

def spells_self(w):
  match w:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      Lemma.and_true_intro(Nat.is_eq(x, x), S.spells(xs, x <> xs, 1n), Lemma.nat_eq_refl(x), spells_unshift(xs, x, xs, 0n, spells_self(xs)))

law spells_own:
  for +f: +List<Core.Tree>
  for +w: +List<Nat>
  for +e: {Core.leaves(f) == w : +List<Nat>}
  {S.spells(Core.leaves(f), w, 0n) == True{} : Bool}

def spells_own(f, w, e):
  %Equal.sym(+List<Nat>, Core.leaves(f), w, e) : {S.spells(_, w, 0n) == True{} : Bool}
  spells_self(w)

# A forest that reads all of w derives w.
law derives_of:
  for +f: +List<Core.Tree>
  for +items: +List<Core.Sym>
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +r: {Core.reads(f, grammar, items, w, 0n) == True{} : Bool}
  for +l: {List.length(&2, Nat, Core.leaves(f)) == List.length(&2, Nat, w) : Nat}
  Core.Derives(grammar, items, w)

def derives_of(f, items, grammar, w, r, l):
  +fit = reads_fits(f, items, grammar, w, 0n, r)
  +lv = S.spells_eq(Core.leaves(f), w, S.reads_spells(f, items, grammar, w, 0n, r), l)
  {(f, (fit, lv)) : Core.Derives(grammar, items, w)}

# ======== THREE-VALUED ANSWERS ========

def TriIs(t: Guard.Tri, u: Guard.Tri) -> Type:
  {t == u : Guard.Tri}

law no_not_yes:
  for +e: {Guard.No{} == Guard.Yes{} : Guard.Tri}
  Empty

def no_not_yes(e):
  Lemma.false_is_not_true(Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Guard.No{}, Guard.Yes{}, e))

law unknown_not_yes:
  for +e: {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}
  Empty

def unknown_not_yes(e):
  Lemma.false_is_not_true(Equal.cong(Guard.Tri, Bool, v => Guard.isYes(v), Guard.Unknown{}, Guard.Yes{}, e))

def isNo(t: Guard.Tri) -> Bool:
  match t:
    case Guard.No{}:
      True{}
    case _:
      False{}

law yes_not_no:
  for +e: {Guard.Yes{} == Guard.No{} : Guard.Tri}
  Empty

def yes_not_no(e):
  Lemma.false_is_not_true(Equal.cong(Guard.Tri, Bool, v => isNo(v), Guard.Yes{}, Guard.No{}, e))

law unknown_not_no:
  for +e: {Guard.Unknown{} == Guard.No{} : Guard.Tri}
  Empty

def unknown_not_no(e):
  Lemma.false_is_not_true(Equal.cong(Guard.Tri, Bool, v => isNo(v), Guard.Unknown{}, Guard.No{}, e))

# ======== A STEP EQUALS ITSELF ========

law bsr_eq_refl:
  for b: Core.Bsr
  {Core.bsrEq(b, b) == True{} : Bool}

def bsr_eq_refl(b):
  match b:
    case Core.Bsr{+q, +d, +i, +k, +j}:
      Lemma.and_true_intro(Nat.is_eq(q, q), Bool.and(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)))), Lemma.nat_eq_refl(q),
        Lemma.and_true_intro(Nat.is_eq(d, d), Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j))), Lemma.nat_eq_refl(d),
          Lemma.and_true_intro(Nat.is_eq(i, i), Bool.and(Nat.is_eq(k, k), Nat.is_eq(j, j)), Lemma.nat_eq_refl(i),
            Lemma.and_true_intro(Nat.is_eq(k, k), Nat.is_eq(j, j), Lemma.nat_eq_refl(k), Lemma.nat_eq_refl(j)))))


# ======== DOES PRODUCTION q DERIVE w? ========

law yes_if_true:
  for c: Bool
  for +e: {Guard.yesIf(c) == Guard.Yes{} : Guard.Tri}
  {c == True{} : Bool}

def yes_if_true(c, e):
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, unknown_not_yes(e))

law yes_if_not_no:
  for c: Bool
  for +e: {Guard.yesIf(c) == Guard.No{} : Guard.Tri}
  Empty

def yes_if_not_no(c, e):
  match c:
    case True{}:
      yes_not_no(e)
    case False{}:
      unknown_not_no(e)

law no_if_true:
  for c: Bool
  for +e: {Guard.noIf(c) == Guard.No{} : Guard.Tri}
  {c == True{} : Bool}

def no_if_true(c, e):
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, unknown_not_no(e))

law no_if_not_yes:
  for c: Bool
  for +e: {Guard.noIf(c) == Guard.Yes{} : Guard.Tri}
  Empty

def no_if_not_yes(c, e):
  match c:
    case True{}:
      no_not_yes(e)
    case False{}:
      unknown_not_yes(e)

def found_yes(b: Bool, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>, +segs: +List<CL.Seg>,
  +e: {Guard.foundPick(b, grammar, q, w, segs) == Guard.Yes{} : Guard.Tri}) -> Core.Derives(grammar, Core.rhsOf(grammar, q), w):
  match b:
    case True{}:
      +f = CL.forestAt(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs)
      +ok = yes_if_true(Guard.forestOk(grammar, q, w, f), e)
      +r = Lemma.and_true_left(Core.reads(f, grammar, Core.rhsOf(grammar, q), w, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves(f)), List.length(&2, Nat, w)), ok)
      +l = Lemma.nat_eq_sound(List.length(&2, Nat, Core.leaves(f)), List.length(&2, Nat, w), Lemma.and_true_right_side(Core.reads(f, grammar, Core.rhsOf(grammar, q), w, 0n), Nat.is_eq(List.length(&2, Nat, Core.leaves(f)), List.length(&2, Nat, w)), ok))
      derives_of(f, Core.rhsOf(grammar, q), grammar, w, r, l)
    case False{}:
      Empty.absurd(Core.Derives(grammar, Core.rhsOf(grammar, q), w), no_if_not_yes(Bool.and(CL.closedAll(segs, grammar, w, segs), CL.hasSeg(q, 0n, 0n, 0n, segs)), e))

# Past the grammar's end a production's right side is empty.
law past_end:
  for g: +List<Core.Production>
  for q: Nat
  for +h: {Core.lhsIs(g, q, Gll.lhsOf(g, q)) == False{} : Bool}
  {Core.rhsOf(g, q) == [] : +List<Core.Sym>}

def past_end(g, q, h):
  match g q:
    case Nil{} +q0:
      {==}
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      Empty.absurd({rhs == [] : +List<Core.Sym>}, Lemma.true_is_not_false(Equal.trans(Bool, True{}, Nat.is_eq(lhs, lhs), False{}, Equal.sym(Bool, Nat.is_eq(lhs, lhs), True{}, Lemma.nat_eq_refl(lhs)), h)))
    case Con{+p, +rest} 1n+(+n):
      past_end(rest, n, h)

law empty_derives:
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +e: {Core.rhsOf(grammar, q) == [] : +List<Core.Sym>}
  Core.Derives(grammar, Core.rhsOf(grammar, q), [])

def empty_derives(grammar, q, e):
  %Equal.sym(+List<Core.Sym>, Core.rhsOf(grammar, q), [], e) : Core.Derives(grammar, _, [])
  {([], ({==}, {==})) : Core.Derives(grammar, [], [])}

def empty_yes(w: +List<Nat>, +grammar: +List<Core.Production>, +q: Nat,
  +e0: {Core.rhsOf(grammar, q) == [] : +List<Core.Sym>},
  +e: {Guard.emptyTri(w) == Guard.Yes{} : Guard.Tri}) -> Core.Derives(grammar, Core.rhsOf(grammar, q), w):
  match w:
    case Nil{}:
      empty_derives(grammar, q, e0)
    case Con{+x, +rest}:
      Empty.absurd(Core.Derives(grammar, Core.rhsOf(grammar, q), x <> rest), no_not_yes(e))

def real_yes(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>,
  +eb: {b == Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) : Bool},
  +e: {Guard.rhsPick(b, fuel, grammar, q, w) == Guard.Yes{} : Guard.Tri}) -> Core.Derives(grammar, Core.rhsOf(grammar, q), w):
  match b:
    case True{}:
      found_yes(CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), CL.segsFrom(fuel, grammar, w, q, 0n)), grammar, q, w, CL.segsFrom(fuel, grammar, w, q, 0n), e)
    case False{}:
      empty_yes(w, grammar, q, past_end(grammar, q, Equal.sym(Bool, False{}, Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)), eb)), e)

# A Yes is right: production q derives w.
law rhs_yes:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +w: +List<Nat>
  for +e: {Guard.rhsTri(fuel, grammar, q, w) == Guard.Yes{} : Guard.Tri}
  Core.Derives(grammar, Core.rhsOf(grammar, q), w)

def rhs_yes(fuel, grammar, q, w, e):
  real_yes(Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)), fuel, grammar, q, w, {==}, e)

def end_at_w(+grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>, +segs: +List<CL.Seg>, +f: +List<Core.Tree>, +lv: {Core.leaves(f) == w : +List<Nat>},
  +h: {CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), G.endOf(f, 0n), segs) == True{} : Bool}) -> {CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs) == True{} : Bool}:
  +en = Equal.trans(Nat, G.endOf(f, 0n), List.length(&2, Nat, Core.leaves(f)), List.length(&2, Nat, w), G.end_eq(f, 0n), Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), Core.leaves(f), w, lv))
  %en : {CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), _, segs) == True{} : Bool}
  h

# A closed set with q's start: a forest of q's right side over w completes q in a segment.
def closed_has(+grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>, +segs: +List<CL.Seg>,
  +c: {Bool.and(CL.closedAll(segs, grammar, w, segs), CL.hasSeg(q, 0n, 0n, 0n, segs)) == True{} : Bool},
  d: Core.Derives(grammar, Core.rhsOf(grammar, q), w)) -> {CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs) == True{} : Bool}:
  match d:
    case (f0, (fit0, lv0)):
      +f = f0
      +lv = lv0
      +rf = fits_reads(f, Core.rhsOf(grammar, q), grammar, w, 0n, fit0, spells_own(f, w, lv))
      end_at_w(grammar, q, w, segs, f, lv,
        PCL.walk(f, Core.rhsOf(grammar, q), grammar, w, segs, q, 0n, 0n, 0n, {==}, {==}, rf,
          Lemma.and_true_right_side(CL.closedAll(segs, grammar, w, segs), CL.hasSeg(q, 0n, 0n, 0n, segs), c),
          Lemma.and_true_left(CL.closedAll(segs, grammar, w, segs), CL.hasSeg(q, 0n, 0n, 0n, segs), c)))

def found_no(b: Bool, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>, +segs: +List<CL.Seg>,
  +eb: {CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs) == b : Bool},
  +e: {Guard.foundPick(b, grammar, q, w, segs) == Guard.No{} : Guard.Tri},
  d: Core.Derives(grammar, Core.rhsOf(grammar, q), w)) -> Empty:
  match b:
    case True{}:
      yes_if_not_no(Guard.forestOk(grammar, q, w, CL.forestAt(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs)), e)
    case False{}:
      Lemma.false_is_not_true(Equal.trans(Bool, False{}, CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs), True{}, Equal.sym(Bool, CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), segs), False{}, eb),
        closed_has(grammar, q, w, segs, no_if_true(Bool.and(CL.closedAll(segs, grammar, w, segs), CL.hasSeg(q, 0n, 0n, 0n, segs)), e), d)))

def empty_no(f: +List<Core.Tree>, w: +List<Nat>, +grammar: +List<Core.Production>,
  +e: {Guard.emptyTri(w) == Guard.No{} : Guard.Tri},
  +fit: {Core.fits(f, grammar, []) == True{} : Bool},
  +lv: {Core.leaves(f) == w : +List<Nat>}) -> Empty:
  match f w:
    case Nil{} Nil{}:
      yes_not_no(e)
    case Nil{} Con{+x, +rest}:
      Lemma.nil_is_not_cons(x, rest, lv)
    case Con{Core.Leaf{+a}, +ts} +w0:
      Lemma.false_is_not_true(fit)
    case Con{Core.Node{+q, +ch}, +ts} +w0:
      Lemma.false_is_not_true(fit)

law past_fits:
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +f: +List<Core.Tree>
  for +e0: {Core.rhsOf(grammar, q) == [] : +List<Core.Sym>}
  for +fit: {Core.fits(f, grammar, Core.rhsOf(grammar, q)) == True{} : Bool}
  {Core.fits(f, grammar, []) == True{} : Bool}

def past_fits(grammar, q, f, e0, fit):
  %e0 : {Core.fits(f, grammar, _) == True{} : Bool}
  fit

def past_no(+grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>,
  +e0: {Core.rhsOf(grammar, q) == [] : +List<Core.Sym>},
  +e: {Guard.emptyTri(w) == Guard.No{} : Guard.Tri},
  d: Core.Derives(grammar, Core.rhsOf(grammar, q), w)) -> Empty:
  match d:
    case (f0, (fit0, lv0)):
      +f = f0
      empty_no(f, w, grammar, e, past_fits(grammar, q, f, e0, fit0), lv0)

def real_no(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +w: +List<Nat>,
  +eb: {b == Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)) : Bool},
  +e: {Guard.rhsPick(b, fuel, grammar, q, w) == Guard.No{} : Guard.Tri},
  d: Core.Derives(grammar, Core.rhsOf(grammar, q), w)) -> Empty:
  match b:
    case True{}:
      found_no(CL.hasSeg(q, 0n, List.length(&2, Core.Sym, Core.rhsOf(grammar, q)), List.length(&2, Nat, w), CL.segsFrom(fuel, grammar, w, q, 0n)), grammar, q, w, CL.segsFrom(fuel, grammar, w, q, 0n), {==}, e, d)
    case False{}:
      past_no(grammar, q, w, past_end(grammar, q, Equal.sym(Bool, False{}, Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)), eb)), e, d)

# A No is right: production q does not derive w.
law rhs_no:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +w: +List<Nat>
  for +e: {Guard.rhsTri(fuel, grammar, q, w) == Guard.No{} : Guard.Tri}
  for d: Core.Derives(grammar, Core.rhsOf(grammar, q), w)
  Empty

def rhs_no(fuel, grammar, q, w, e, d):
  real_no(Core.lhsIs(grammar, q, Gll.lhsOf(grammar, q)), fuel, grammar, q, w, {==}, e, d)

# ======== COMBINING ANSWERS ========

law or_yes_cases:
  for a: Guard.Tri
  for b: Guard.Tri
  for +e: {Guard.orTri(a, b) == Guard.Yes{} : Guard.Tri}
  Either<{a == Guard.Yes{} : Guard.Tri}, {b == Guard.Yes{} : Guard.Tri}>

def or_yes_cases(a, b, e):
  match a b:
    case Guard.Yes{} +b0:
      Inl{{==}}
    case Guard.No{} Guard.Yes{}:
      Inr{{==}}
    case Guard.Unknown{} Guard.Yes{}:
      Inr{{==}}
    case Guard.No{} Guard.No{}:
      Empty.absurd(Either<{Guard.No{} == Guard.Yes{} : Guard.Tri}, {Guard.No{} == Guard.Yes{} : Guard.Tri}>, no_not_yes(e))
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.No{} == Guard.Yes{} : Guard.Tri}, {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}>, unknown_not_yes(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, {Guard.No{} == Guard.Yes{} : Guard.Tri}>, unknown_not_yes(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}>, unknown_not_yes(e))

law or_no:
  for a: Guard.Tri
  for b: Guard.Tri
  for +e: {Guard.orTri(a, b) == Guard.No{} : Guard.Tri}
  {a == Guard.No{} : Guard.Tri} & {b == Guard.No{} : Guard.Tri}

def or_no(a, b, e):
  match a b:
    case Guard.No{} Guard.No{}:
      ({==}, {==})
    case Guard.Yes{} Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri} & {Guard.Yes{} == Guard.No{} : Guard.Tri}, yes_not_no(e))
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri} & {Guard.No{} == Guard.No{} : Guard.Tri}, yes_not_no(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri} & {Guard.Unknown{} == Guard.No{} : Guard.Tri}, yes_not_no(e))
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri} & {Guard.Yes{} == Guard.No{} : Guard.Tri}, yes_not_no(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri} & {Guard.Yes{} == Guard.No{} : Guard.Tri}, yes_not_no(e))
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.No{} == Guard.No{} : Guard.Tri} & {Guard.Unknown{} == Guard.No{} : Guard.Tri}, unknown_not_no(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri} & {Guard.No{} == Guard.No{} : Guard.Tri}, unknown_not_no(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri} & {Guard.Unknown{} == Guard.No{} : Guard.Tri}, unknown_not_no(e))

law and_yes:
  for a: Guard.Tri
  for b: Guard.Tri
  for +e: {Guard.andTri(a, b) == Guard.Yes{} : Guard.Tri}
  {a == Guard.Yes{} : Guard.Tri} & {b == Guard.Yes{} : Guard.Tri}

def and_yes(a, b, e):
  match a b:
    case Guard.Yes{} Guard.Yes{}:
      ({==}, {==})
    case Guard.No{} Guard.Yes{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri} & {Guard.Yes{} == Guard.Yes{} : Guard.Tri}, no_not_yes(e))
    case Guard.No{} Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri} & {Guard.No{} == Guard.Yes{} : Guard.Tri}, no_not_yes(e))
    case Guard.No{} Guard.Unknown{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri} & {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, no_not_yes(e))
    case Guard.Yes{} Guard.No{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri} & {Guard.No{} == Guard.Yes{} : Guard.Tri}, no_not_yes(e))
    case Guard.Unknown{} Guard.No{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri} & {Guard.No{} == Guard.Yes{} : Guard.Tri}, no_not_yes(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd({Guard.Yes{} == Guard.Yes{} : Guard.Tri} & {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, unknown_not_yes(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri} & {Guard.Yes{} == Guard.Yes{} : Guard.Tri}, unknown_not_yes(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri} & {Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, unknown_not_yes(e))

law and_no_cases:
  for a: Guard.Tri
  for b: Guard.Tri
  for +e: {Guard.andTri(a, b) == Guard.No{} : Guard.Tri}
  Either<{a == Guard.No{} : Guard.Tri}, {b == Guard.No{} : Guard.Tri}>

def and_no_cases(a, b, e):
  match a b:
    case Guard.No{} +b0:
      Inl{{==}}
    case Guard.Yes{} Guard.No{}:
      Inr{{==}}
    case Guard.Unknown{} Guard.No{}:
      Inr{{==}}
    case Guard.Yes{} Guard.Yes{}:
      Empty.absurd(Either<{Guard.Yes{} == Guard.No{} : Guard.Tri}, {Guard.Yes{} == Guard.No{} : Guard.Tri}>, yes_not_no(e))
    case Guard.Yes{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.Yes{} == Guard.No{} : Guard.Tri}, {Guard.Unknown{} == Guard.No{} : Guard.Tri}>, unknown_not_no(e))
    case Guard.Unknown{} Guard.Yes{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.No{} : Guard.Tri}, {Guard.Yes{} == Guard.No{} : Guard.Tri}>, unknown_not_no(e))
    case Guard.Unknown{} Guard.Unknown{}:
      Empty.absurd(Either<{Guard.Unknown{} == Guard.No{} : Guard.Tri}, {Guard.Unknown{} == Guard.No{} : Guard.Tri}>, unknown_not_no(e))

law not_yes:
  for a: Guard.Tri
  for +e: {Guard.notTri(a) == Guard.Yes{} : Guard.Tri}
  {a == Guard.No{} : Guard.Tri}

def not_yes(a, e):
  match a:
    case Guard.No{}:
      {==}
    case Guard.Yes{}:
      Empty.absurd({Guard.Yes{} == Guard.No{} : Guard.Tri}, no_not_yes(e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.No{} : Guard.Tri}, unknown_not_yes(e))

law not_no:
  for a: Guard.Tri
  for +e: {Guard.notTri(a) == Guard.No{} : Guard.Tri}
  {a == Guard.Yes{} : Guard.Tri}

def not_no(a, e):
  match a:
    case Guard.Yes{}:
      {==}
    case Guard.No{}:
      Empty.absurd({Guard.No{} == Guard.Yes{} : Guard.Tri}, yes_not_no(e))
    case Guard.Unknown{}:
      Empty.absurd({Guard.Unknown{} == Guard.Yes{} : Guard.Tri}, unknown_not_no(e))

# ======== DOES NONTERMINAL x DERIVE w? ========

def nt_node(+grammar: +List<Core.Production>, +q: Nat, +x: Nat, +w: +List<Nat>,
  +lhs: {Core.lhsIs(grammar, q, x) == True{} : Bool},
  d: Core.Derives(grammar, Core.rhsOf(grammar, q), w)) -> Core.Derives(grammar, Guard.nt(x), w):
  match d:
    case (f0, (fit0, lv0)):
      +f = f0
      +fit = fit0
      +lv = lv0
      +head = {Bool.and(Core.lhsIs(grammar, q, x), True{}) : Bool}
      +fits = Lemma.and_true_intro(Bool.and(head, Core.fits(f, grammar, Core.rhsOf(grammar, q))), True{},
        Lemma.and_true_intro(head, Core.fits(f, grammar, Core.rhsOf(grammar, q)), Lemma.and_true_intro(Core.lhsIs(grammar, q, x), True{}, lhs, {==}), fit), {==})
      +leaves = Equal.trans(+List<Nat>, List.append(&2, Nat, Core.leaves(f), []), Core.leaves(f), w, Lemma.append_nil_right(Core.leaves(f)), lv)
      {([Core.Node{q, f}], (fits, leaves)) : Core.Derives(grammar, Guard.nt(x), w)}

def pick_yes(b: Bool, +fuel: Nat, +grammar: +List<Core.Production>, +q: Nat, +x: Nat, +w: +List<Nat>,
  +eb: {b == Core.lhsIs(grammar, q, x) : Bool},
  +e: {Guard.ntPick(b, fuel, grammar, q, w) == Guard.Yes{} : Guard.Tri}) -> Core.Derives(grammar, Guard.nt(x), w):
  match b:
    case True{}:
      nt_node(grammar, q, x, w, Equal.sym(Bool, True{}, Core.lhsIs(grammar, q, x), eb), rhs_yes(fuel, grammar, q, w, e))
    case False{}:
      Empty.absurd(Core.Derives(grammar, Guard.nt(x), w), no_not_yes(e))

def nt_pick_yes(+fuel: Nat, +grammar: +List<Core.Production>, +x: Nat, +q: Nat, +w: +List<Nat>, +rest: +List<Core.Production>,
  cases: Either<{Guard.ntPick(Core.lhsIs(grammar, q, x), fuel, grammar, q, w) == Guard.Yes{} : Guard.Tri}, {Guard.ntFrom(rest, fuel, grammar, x, 1n+q, w) == Guard.Yes{} : Guard.Tri}>,
  later: {Guard.ntFrom(rest, fuel, grammar, x, 1n+q, w) == Guard.Yes{} : Guard.Tri} -> Core.Derives(grammar, Guard.nt(x), w)) -> Core.Derives(grammar, Guard.nt(x), w):
  match cases:
    case Inl{+e}:
      pick_yes(Core.lhsIs(grammar, q, x), fuel, grammar, q, x, w, {==}, e)
    case Inr{h}:
      later(h)

law nt_from_yes:
  for prods: +List<Core.Production>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +q: Nat
  for +w: +List<Nat>
  for +e: {Guard.ntFrom(prods, fuel, grammar, x, q, w) == Guard.Yes{} : Guard.Tri}
  Core.Derives(grammar, Guard.nt(x), w)

def nt_from_yes(prods, fuel, grammar, x, q, w, e):
  match prods:
    case Nil{}:
      Empty.absurd(Core.Derives(grammar, Guard.nt(x), w), no_not_yes(e))
    case Con{+p, +rest}:
      nt_pick_yes(fuel, grammar, x, q, w, rest, or_yes_cases(Guard.ntPick(Core.lhsIs(grammar, q, x), fuel, grammar, q, w), Guard.ntFrom(rest, fuel, grammar, x, 1n+q, w), e),
        later => nt_from_yes(rest, fuel, grammar, x, 1n+q, w, later))

law nt_yes:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +w: +List<Nat>
  for +e: {Guard.ntTri(fuel, grammar, x, w) == Guard.Yes{} : Guard.Tri}
  Core.Derives(grammar, Guard.nt(x), w)

def nt_yes(fuel, grammar, x, w, e):
  nt_from_yes(grammar, fuel, grammar, x, 0n, w, e)

law pick_at_zero:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +base: Nat
  for +w: +List<Nat>
  for +h: {Guard.ntPick(Core.lhsIs(grammar, base, x), fuel, grammar, base, w) == Guard.No{} : Guard.Tri}
  {Guard.ntPick(Core.lhsIs(grammar, Nat.add(base, 0n), x), fuel, grammar, Nat.add(base, 0n), w) == Guard.No{} : Guard.Tri}

def pick_at_zero(fuel, grammar, x, base, w, h):
  %Equal.sym(Nat, Nat.add(base, 0n), base, Lemma.add_zero_right(base)) : {Guard.ntPick(Core.lhsIs(grammar, _, x), fuel, grammar, _, w) == Guard.No{} : Guard.Tri}
  h

law pick_at_succ:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +base: Nat
  for +n: Nat
  for +w: +List<Nat>
  for +h: {Guard.ntPick(Core.lhsIs(grammar, 1n+Nat.add(base, n), x), fuel, grammar, 1n+Nat.add(base, n), w) == Guard.No{} : Guard.Tri}
  {Guard.ntPick(Core.lhsIs(grammar, Nat.add(base, 1n+n), x), fuel, grammar, Nat.add(base, 1n+n), w) == Guard.No{} : Guard.Tri}

def pick_at_succ(fuel, grammar, x, base, n, w, h):
  %Equal.sym(Nat, Nat.add(base, 1n+n), 1n+Nat.add(base, n), Lemma.add_succ_right(base, n)) : {Guard.ntPick(Core.lhsIs(grammar, _, x), fuel, grammar, _, w) == Guard.No{} : Guard.Tri}
  h

def first_no(+a: Guard.Tri, +b: Guard.Tri, p: {a == Guard.No{} : Guard.Tri} & {b == Guard.No{} : Guard.Tri}) -> {a == Guard.No{} : Guard.Tri}:
  match p:
    case (x, y):
      x


def second_no(+a: Guard.Tri, +b: Guard.Tri, p: {a == Guard.No{} : Guard.Tri} & {b == Guard.No{} : Guard.Tri}) -> {b == Guard.No{} : Guard.Tri}:
  match p:
    case (x, y):
      y


# A No for x is a No for each of its productions.
law nt_no_at:
  for g: +List<Core.Production>
  for q: Nat
  for +x: Nat
  for +base: Nat
  for +w: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +h: {Core.lhsIs(g, q, x) == True{} : Bool}
  for +e: {Guard.ntFrom(g, fuel, grammar, x, base, w) == Guard.No{} : Guard.Tri}
  {Guard.ntPick(Core.lhsIs(grammar, Nat.add(base, q), x), fuel, grammar, Nat.add(base, q), w) == Guard.No{} : Guard.Tri}

def nt_no_at(g, q, x, base, w, fuel, grammar, h, e):
  match g q:
    case Nil{} +q0:
      Empty.absurd({Guard.ntPick(Core.lhsIs(grammar, Nat.add(base, q0), x), fuel, grammar, Nat.add(base, q0), w) == Guard.No{} : Guard.Tri}, Lemma.false_is_not_true(h))
    case Con{Core.Production{+lhs, +rhs}, +rest} 0n:
      both = or_no(Guard.ntPick(Core.lhsIs(grammar, base, x), fuel, grammar, base, w), Guard.ntFrom(rest, fuel, grammar, x, 1n+base, w), e)
      pick_at_zero(fuel, grammar, x, base, w, first_no(Guard.ntPick(Core.lhsIs(grammar, base, x), fuel, grammar, base, w), Guard.ntFrom(rest, fuel, grammar, x, 1n+base, w), both))
    case Con{Core.Production{+lhs, +rhs}, +rest} 1n+(+n):
      both = or_no(Guard.ntPick(Core.lhsIs(grammar, base, x), fuel, grammar, base, w), Guard.ntFrom(rest, fuel, grammar, x, 1n+base, w), e)
      pick_at_succ(fuel, grammar, x, base, n, w, nt_no_at(rest, n, x, 1n+base, w, fuel, grammar, h, second_no(Guard.ntPick(Core.lhsIs(grammar, base, x), fuel, grammar, base, w), Guard.ntFrom(rest, fuel, grammar, x, 1n+base, w), both)))

law pick_true_no:
  for b: Bool
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +w: +List<Nat>
  for +eb: {b == True{} : Bool}
  for +e: {Guard.ntPick(b, fuel, grammar, q, w) == Guard.No{} : Guard.Tri}
  {Guard.rhsTri(fuel, grammar, q, w) == Guard.No{} : Guard.Tri}

def pick_true_no(b, fuel, grammar, q, w, eb, e):
  match b:
    case True{}:
      e
    case False{}:
      Empty.absurd({Guard.rhsTri(fuel, grammar, q, w) == Guard.No{} : Guard.Tri}, Lemma.false_is_not_true(eb))

law nt_no_more:
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +x: Nat
  for +f: +List<Core.Tree>
  for t2: Core.Tree
  for +r2: +List<Core.Tree>
  for +fit: {Core.fits(Core.Node{q, f} <> t2 <> r2, grammar, Guard.nt(x)) == True{} : Bool}
  Empty

def nt_no_more(grammar, q, x, f, t2, r2, fit):
  match t2:
    case Core.Leaf{+a}:
      Lemma.false_is_not_true(Lemma.and_true_right_side(Bool.and(Bool.and(Core.lhsIs(grammar, q, x), True{}), Core.fits(f, grammar, Core.rhsOf(grammar, q))), False{}, fit))
    case Core.Node{+q2, +f2}:
      Lemma.false_is_not_true(Lemma.and_true_right_side(Bool.and(Bool.and(Core.lhsIs(grammar, q, x), True{}), Core.fits(f, grammar, Core.rhsOf(grammar, q))), False{}, fit))

def nt_no_tree(forest: +List<Core.Tree>, +fuel: Nat, +grammar: +List<Core.Production>, +x: Nat, +w: +List<Nat>,
  +e: {Guard.ntTri(fuel, grammar, x, w) == Guard.No{} : Guard.Tri},
  +fit: {Core.fits(forest, grammar, Guard.nt(x)) == True{} : Bool},
  +lv: {Core.leaves(forest) == w : +List<Nat>}) -> Empty:
  match forest:
    case Con{Core.Node{+q, +f}, Nil{}}:
      +head = {Bool.and(Core.lhsIs(grammar, q, x), Core.needOk(Core.Anything{}, Core.width(Core.Node{q, f}))) : Bool}
      +own = {Bool.and(head, Core.fits(f, grammar, Core.rhsOf(grammar, q))) : Bool}
      +left = Lemma.and_true_left(own, True{}, fit)
      +lhs = Lemma.and_true_left(Core.lhsIs(grammar, q, x), True{}, Lemma.and_true_left(head, Core.fits(f, grammar, Core.rhsOf(grammar, q)), left))
      +ff = Lemma.and_true_right_side(head, Core.fits(f, grammar, Core.rhsOf(grammar, q)), left)
      +lf = Equal.trans(+List<Nat>, Core.leaves(f), List.append(&2, Nat, Core.leaves(f), []), w, Equal.sym(+List<Nat>, List.append(&2, Nat, Core.leaves(f), []), Core.leaves(f), Lemma.append_nil_right(Core.leaves(f))), lv)
      +pick = nt_no_at(grammar, q, x, 0n, w, fuel, grammar, lhs, e)
      rhs_no(fuel, grammar, q, w, pick_true_no(Core.lhsIs(grammar, q, x), fuel, grammar, q, w, lhs, pick), (f, (ff, lf)))
    case Nil{}:
      Lemma.false_is_not_true(fit)
    case Con{Core.Leaf{+a}, +ts}:
      Lemma.false_is_not_true(fit)
    case Con{Core.Node{+q, +f}, Con{+t2, +r2}}:
      nt_no_more(grammar, q, x, f, t2, r2, fit)

law nt_no:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +w: +List<Nat>
  for +e: {Guard.ntTri(fuel, grammar, x, w) == Guard.No{} : Guard.Tri}
  for d: Core.Derives(grammar, Guard.nt(x), w)
  Empty

def nt_no(fuel, grammar, x, w, e, d):
  match d:
    case (forest0, (fit0, lv0)):
      +forest = forest0
      nt_no_tree(forest, fuel, grammar, x, w, e, fit0, lv0)

# ======== DOES x DERIVE A PREFIX OF WHAT FOLLOWS? ========

law take_drop:
  for n: Nat
  for xs: +List<Nat>
  {List.append(&2, Nat, Lemma.takeN(n, xs), Lemma.dropN(n, xs)) == xs : +List<Nat>}

def take_drop(n, xs):
  match n xs:
    case 0n +ys:
      {==}
    case 1n+(+p) Nil{}:
      {==}
    case 1n+(+p) Con{+x, +rest}:
      Equal.cong(+List<Nat>, +List<Nat>, v => x <> v, List.append(&2, Nat, Lemma.takeN(p, rest), Lemma.dropN(p, rest)), rest, take_drop(p, rest))

def ahead_pick(+fuel: Nat, +grammar: +List<Core.Production>, +x: Nat, +ahead: +List<Nat>, +p: Nat,
  cases: Either<{Guard.ntTri(fuel, grammar, x, Lemma.takeN(1n+p, ahead)) == Guard.Yes{} : Guard.Tri}, {Guard.aheadFrom(p, fuel, grammar, x, ahead) == Guard.Yes{} : Guard.Tri}>,
  later: {Guard.aheadFrom(p, fuel, grammar, x, ahead) == Guard.Yes{} : Guard.Tri} -> Guard.DerivesAhead(grammar, x, ahead)) -> Guard.DerivesAhead(grammar, x, ahead):
  match cases:
    case Inl{+e}:
      +pre = Lemma.takeN(1n+p, ahead)
      +post = Lemma.dropN(1n+p, ahead)
      +split = take_drop(1n+p, ahead)
      {(pre, (post, (split, nt_yes(fuel, grammar, x, pre, e)))) : Guard.DerivesAhead(grammar, x, ahead)}
    case Inr{h}:
      later(h)

law ahead_yes:
  for m: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +ahead: +List<Nat>
  for +e: {Guard.aheadFrom(m, fuel, grammar, x, ahead) == Guard.Yes{} : Guard.Tri}
  Guard.DerivesAhead(grammar, x, ahead)

def ahead_yes(m, fuel, grammar, x, ahead, e):
  match m:
    case 0n:
      {([], (ahead, ({==}, nt_yes(fuel, grammar, x, [], e)))) : Guard.DerivesAhead(grammar, x, ahead)}
    case 1n+(+p):
      ahead_pick(fuel, grammar, x, ahead, p, or_yes_cases(Guard.ntTri(fuel, grammar, x, Lemma.takeN(1n+p, ahead)), Guard.aheadFrom(p, fuel, grammar, x, ahead), e),
        later => ahead_yes(p, fuel, grammar, x, ahead, later))

law head_no:
  for m: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +ahead: +List<Nat>
  for +e: {Guard.aheadFrom(m, fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  {Guard.ntTri(fuel, grammar, x, Lemma.takeN(m, ahead)) == Guard.No{} : Guard.Tri}

def head_no(m, fuel, grammar, x, ahead, e):
  match m:
    case 0n:
      e
    case 1n+(+p):
      first_no(Guard.ntTri(fuel, grammar, x, Lemma.takeN(1n+p, ahead)), Guard.aheadFrom(p, fuel, grammar, x, ahead),
        or_no(Guard.ntTri(fuel, grammar, x, Lemma.takeN(1n+p, ahead)), Guard.aheadFrom(p, fuel, grammar, x, ahead), e))

law from_at_zero:
  for +m: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +ahead: +List<Nat>
  for +e: {Guard.aheadFrom(Nat.add(m, 0n), fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  {Guard.aheadFrom(m, fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}

def from_at_zero(m, fuel, grammar, x, ahead, e):
  %Lemma.add_zero_right(m) : {Guard.aheadFrom(_, fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  e

law from_at_succ:
  for +m: Nat
  for +r: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +ahead: +List<Nat>
  for +e: {Guard.aheadFrom(Nat.add(m, 1n+r), fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  {Guard.aheadFrom(1n+Nat.add(m, r), fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}

def from_at_succ(m, r, fuel, grammar, x, ahead, e):
  %Lemma.add_succ_right(m, r) : {Guard.aheadFrom(_, fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  e

# A No over prefixes up to length m + r is a No for the prefix of length m.
law ahead_no_at:
  for r: Nat
  for +m: Nat
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +ahead: +List<Nat>
  for +e: {Guard.aheadFrom(Nat.add(m, r), fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  {Guard.ntTri(fuel, grammar, x, Lemma.takeN(m, ahead)) == Guard.No{} : Guard.Tri}

def ahead_no_at(r, m, fuel, grammar, x, ahead, e):
  match r:
    case 0n:
      head_no(m, fuel, grammar, x, ahead, from_at_zero(m, fuel, grammar, x, ahead, e))
    case 1n+(+r2):
      +e2 = from_at_succ(m, r2, fuel, grammar, x, ahead, e)
      ahead_no_at(r2, m, fuel, grammar, x, ahead, second_no(Guard.ntTri(fuel, grammar, x, Lemma.takeN(1n+Nat.add(m, r2), ahead)), Guard.aheadFrom(Nat.add(m, r2), fuel, grammar, x, ahead),
        or_no(Guard.ntTri(fuel, grammar, x, Lemma.takeN(1n+Nat.add(m, r2), ahead)), Guard.aheadFrom(Nat.add(m, r2), fuel, grammar, x, ahead), e2)))

law len_split:
  for +pre: +List<Nat>
  for +post: +List<Nat>
  for +ahead: +List<Nat>
  for +eq: {List.append(&2, Nat, pre, post) == ahead : +List<Nat>}
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +e: {Guard.aheadFrom(List.length(&2, Nat, ahead), fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  {Guard.aheadFrom(Nat.add(List.length(&2, Nat, pre), List.length(&2, Nat, post)), fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}

def len_split(pre, post, ahead, eq, fuel, grammar, x, e):
  +l = Equal.trans(Nat, Nat.add(List.length(&2, Nat, pre), List.length(&2, Nat, post)), List.length(&2, Nat, List.append(&2, Nat, pre, post)), List.length(&2, Nat, ahead),
    Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, pre, post)), Nat.add(List.length(&2, Nat, pre), List.length(&2, Nat, post)), Lemma.length_append(pre, post)),
    Equal.cong(+List<Nat>, Nat, v => List.length(&2, Nat, v), List.append(&2, Nat, pre, post), ahead, eq))
  %Equal.sym(Nat, Nat.add(List.length(&2, Nat, pre), List.length(&2, Nat, post)), List.length(&2, Nat, ahead), l) : {Guard.aheadFrom(_, fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  e

law take_pre:
  for +pre: +List<Nat>
  for +post: +List<Nat>
  for +ahead: +List<Nat>
  for +eq: {List.append(&2, Nat, pre, post) == ahead : +List<Nat>}
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +e: {Guard.ntTri(fuel, grammar, x, Lemma.takeN(List.length(&2, Nat, pre), ahead)) == Guard.No{} : Guard.Tri}
  {Guard.ntTri(fuel, grammar, x, pre) == Guard.No{} : Guard.Tri}

def take_pre(pre, post, ahead, eq, fuel, grammar, x, e):
  +tp = Equal.trans(+List<Nat>, Lemma.takeN(List.length(&2, Nat, pre), ahead), Lemma.takeN(List.length(&2, Nat, pre), List.append(&2, Nat, pre, post)), pre,
    Equal.cong(+List<Nat>, +List<Nat>, v => Lemma.takeN(List.length(&2, Nat, pre), v), ahead, List.append(&2, Nat, pre, post), Equal.sym(+List<Nat>, List.append(&2, Nat, pre, post), ahead, eq)),
    Lemma.take_append_length(pre, post))
  %tp : {Guard.ntTri(fuel, grammar, x, _) == Guard.No{} : Guard.Tri}
  e

law ahead_no:
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +x: Nat
  for +ahead: +List<Nat>
  for +e: {Guard.aheadTri(fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}
  for da: Guard.DerivesAhead(grammar, x, ahead)
  Empty

def ahead_no(fuel, grammar, x, ahead, e, da):
  match da:
    case (pre0, (post0, (eq0, d))):
      +pre = pre0
      +post = post0
      +eq = eq0
      +e2 = len_split(pre, post, ahead, eq, fuel, grammar, x, e)
      nt_no(fuel, grammar, x, pre, take_pre(pre, post, ahead, eq, fuel, grammar, x, ahead_no_at(List.length(&2, Nat, post), List.length(&2, Nat, pre), fuel, grammar, x, ahead, e2)), d)

# ======== THE RULES' ANSWERS ========

def all_ahead_pair(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>,
  p: {Guard.aheadTri(fuel, grammar, x, ahead) == Guard.Yes{} : Guard.Tri} & {Guard.allAheadTri(rest, fuel, grammar, ahead) == Guard.Yes{} : Guard.Tri},
  later: {Guard.allAheadTri(rest, fuel, grammar, ahead) == Guard.Yes{} : Guard.Tri} -> Guard.AllAhead(grammar, rest, ahead)) -> Guard.AllAhead(grammar, x <> rest, ahead):
  match p:
    case (a, b):
      (ahead_yes(List.length(&2, Nat, ahead), fuel, grammar, x, ahead, a), later(b))


law all_ahead_yes:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +ahead: +List<Nat>
  for +e: {Guard.allAheadTri(ids, fuel, grammar, ahead) == Guard.Yes{} : Guard.Tri}
  Guard.AllAhead(grammar, ids, ahead)

def all_ahead_yes(ids, fuel, grammar, ahead, e):
  match ids:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      all_ahead_pair(x, rest, fuel, grammar, ahead, and_yes(Guard.aheadTri(fuel, grammar, x, ahead), Guard.allAheadTri(rest, fuel, grammar, ahead), e),
        later => all_ahead_yes(rest, fuel, grammar, ahead, later))

def all_ahead_side(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>,
  cases: Either<{Guard.aheadTri(fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}, {Guard.allAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri}>,
  da: Guard.DerivesAhead(grammar, x, ahead), hr: Guard.AllAhead(grammar, rest, ahead),
  later: {Guard.allAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri} -> Guard.AllAhead(grammar, rest, ahead) -> Empty) -> Empty:
  match cases:
    case Inl{e}:
      ahead_no(fuel, grammar, x, ahead, e, da)
    case Inr{e}:
      later(e, hr)


def all_ahead_split(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>,
  cases: Either<{Guard.aheadTri(fuel, grammar, x, ahead) == Guard.No{} : Guard.Tri}, {Guard.allAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri}>,
  h: Guard.AllAhead(grammar, x <> rest, ahead),
  later: {Guard.allAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri} -> Guard.AllAhead(grammar, rest, ahead) -> Empty) -> Empty:
  match h:
    case (da, hr):
      all_ahead_side(x, rest, fuel, grammar, ahead, cases, da, hr, later)


law all_ahead_no:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +ahead: +List<Nat>
  for +e: {Guard.allAheadTri(ids, fuel, grammar, ahead) == Guard.No{} : Guard.Tri}
  for h: Guard.AllAhead(grammar, ids, ahead)
  Empty

def all_ahead_no(ids, fuel, grammar, ahead, e, h):
  match ids:
    case Nil{}:
      Empty.absurd(Empty, yes_not_no(e))
    case Con{+x, +rest}:
      all_ahead_split(x, rest, fuel, grammar, ahead, and_no_cases(Guard.aheadTri(fuel, grammar, x, ahead), Guard.allAheadTri(rest, fuel, grammar, ahead), e), h,
        later => hr => all_ahead_no(rest, fuel, grammar, ahead, later, hr))

def none_ahead_pair(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>,
  p: {Guard.notTri(Guard.aheadTri(fuel, grammar, x, ahead)) == Guard.Yes{} : Guard.Tri} & {Guard.noneAheadTri(rest, fuel, grammar, ahead) == Guard.Yes{} : Guard.Tri},
  later: {Guard.noneAheadTri(rest, fuel, grammar, ahead) == Guard.Yes{} : Guard.Tri} -> Guard.NoneAhead(grammar, rest, ahead)) -> Guard.NoneAhead(grammar, x <> rest, ahead):
  match p:
    case (a0, b):
      +a = not_yes(Guard.aheadTri(fuel, grammar, x, ahead), a0)
      (da => ahead_no(fuel, grammar, x, ahead, a, da), later(b))


law none_ahead_yes:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +ahead: +List<Nat>
  for +e: {Guard.noneAheadTri(ids, fuel, grammar, ahead) == Guard.Yes{} : Guard.Tri}
  Guard.NoneAhead(grammar, ids, ahead)

def none_ahead_yes(ids, fuel, grammar, ahead, e):
  match ids:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      none_ahead_pair(x, rest, fuel, grammar, ahead, and_yes(Guard.notTri(Guard.aheadTri(fuel, grammar, x, ahead)), Guard.noneAheadTri(rest, fuel, grammar, ahead), e),
        later => none_ahead_yes(rest, fuel, grammar, ahead, later))

def none_ahead_side(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>,
  cases: Either<{Guard.notTri(Guard.aheadTri(fuel, grammar, x, ahead)) == Guard.No{} : Guard.Tri}, {Guard.noneAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri}>,
  notAhead: Guard.DerivesAhead(grammar, x, ahead) -> Empty, hr: Guard.NoneAhead(grammar, rest, ahead),
  later: {Guard.noneAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri} -> Guard.NoneAhead(grammar, rest, ahead) -> Empty) -> Empty:
  match cases:
    case Inl{e}:
      notAhead(ahead_yes(List.length(&2, Nat, ahead), fuel, grammar, x, ahead, not_no(Guard.aheadTri(fuel, grammar, x, ahead), e)))
    case Inr{e}:
      later(e, hr)


def none_ahead_split(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +ahead: +List<Nat>,
  cases: Either<{Guard.notTri(Guard.aheadTri(fuel, grammar, x, ahead)) == Guard.No{} : Guard.Tri}, {Guard.noneAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri}>,
  h: Guard.NoneAhead(grammar, x <> rest, ahead),
  later: {Guard.noneAheadTri(rest, fuel, grammar, ahead) == Guard.No{} : Guard.Tri} -> Guard.NoneAhead(grammar, rest, ahead) -> Empty) -> Empty:
  match h:
    case (notAhead, hr):
      none_ahead_side(x, rest, fuel, grammar, ahead, cases, notAhead, hr, later)


law none_ahead_no:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +ahead: +List<Nat>
  for +e: {Guard.noneAheadTri(ids, fuel, grammar, ahead) == Guard.No{} : Guard.Tri}
  for h: Guard.NoneAhead(grammar, ids, ahead)
  Empty

def none_ahead_no(ids, fuel, grammar, ahead, e, h):
  match ids:
    case Nil{}:
      Empty.absurd(Empty, yes_not_no(e))
    case Con{+x, +rest}:
      none_ahead_split(x, rest, fuel, grammar, ahead, and_no_cases(Guard.notTri(Guard.aheadTri(fuel, grammar, x, ahead)), Guard.noneAheadTri(rest, fuel, grammar, ahead), e), h,
        later => hr => none_ahead_no(rest, fuel, grammar, ahead, later, hr))

def none_derive_pair(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +w: +List<Nat>,
  p: {Guard.notTri(Guard.ntTri(fuel, grammar, x, w)) == Guard.Yes{} : Guard.Tri} & {Guard.noneDeriveTri(rest, fuel, grammar, w) == Guard.Yes{} : Guard.Tri},
  later: {Guard.noneDeriveTri(rest, fuel, grammar, w) == Guard.Yes{} : Guard.Tri} -> Guard.NoneDerive(grammar, rest, w)) -> Guard.NoneDerive(grammar, x <> rest, w):
  match p:
    case (a0, b):
      +a = not_yes(Guard.ntTri(fuel, grammar, x, w), a0)
      (d => nt_no(fuel, grammar, x, w, a, d), later(b))


law none_derive_yes:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +e: {Guard.noneDeriveTri(ids, fuel, grammar, w) == Guard.Yes{} : Guard.Tri}
  Guard.NoneDerive(grammar, ids, w)

def none_derive_yes(ids, fuel, grammar, w, e):
  match ids:
    case Nil{}:
      Unit{}
    case Con{+x, +rest}:
      none_derive_pair(x, rest, fuel, grammar, w, and_yes(Guard.notTri(Guard.ntTri(fuel, grammar, x, w)), Guard.noneDeriveTri(rest, fuel, grammar, w), e),
        later => none_derive_yes(rest, fuel, grammar, w, later))

def none_derive_side(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +w: +List<Nat>,
  cases: Either<{Guard.notTri(Guard.ntTri(fuel, grammar, x, w)) == Guard.No{} : Guard.Tri}, {Guard.noneDeriveTri(rest, fuel, grammar, w) == Guard.No{} : Guard.Tri}>,
  notD: Core.Derives(grammar, Guard.nt(x), w) -> Empty, hr: Guard.NoneDerive(grammar, rest, w),
  later: {Guard.noneDeriveTri(rest, fuel, grammar, w) == Guard.No{} : Guard.Tri} -> Guard.NoneDerive(grammar, rest, w) -> Empty) -> Empty:
  match cases:
    case Inl{e}:
      notD(nt_yes(fuel, grammar, x, w, not_no(Guard.ntTri(fuel, grammar, x, w), e)))
    case Inr{e}:
      later(e, hr)

# The edge of a node of production q spells w.

def none_derive_split(+x: Nat, +rest: +List<Nat>, +fuel: Nat, +grammar: +List<Core.Production>, +w: +List<Nat>,
  cases: Either<{Guard.notTri(Guard.ntTri(fuel, grammar, x, w)) == Guard.No{} : Guard.Tri}, {Guard.noneDeriveTri(rest, fuel, grammar, w) == Guard.No{} : Guard.Tri}>,
  h: Guard.NoneDerive(grammar, x <> rest, w),
  later: {Guard.noneDeriveTri(rest, fuel, grammar, w) == Guard.No{} : Guard.Tri} -> Guard.NoneDerive(grammar, rest, w) -> Empty) -> Empty:
  match h:
    case (notD, hr):
      none_derive_side(x, rest, fuel, grammar, w, cases, notD, hr, later)


law none_derive_no:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +w: +List<Nat>
  for +e: {Guard.noneDeriveTri(ids, fuel, grammar, w) == Guard.No{} : Guard.Tri}
  for h: Guard.NoneDerive(grammar, ids, w)
  Empty

def none_derive_no(ids, fuel, grammar, w, e, h):
  match ids:
    case Nil{}:
      Empty.absurd(Empty, yes_not_no(e))
    case Con{+x, +rest}:
      none_derive_split(x, rest, fuel, grammar, w, and_no_cases(Guard.notTri(Guard.ntTri(fuel, grammar, x, w)), Guard.noneDeriveTri(rest, fuel, grammar, w), e), h,
        later => hr => none_derive_no(rest, fuel, grammar, w, later, hr))

law edge_yes:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +w: +List<Nat>
  for +e: {Guard.edgeTri(ids, fuel, grammar, q, w) == Guard.Yes{} : Guard.Tri}
  Guard.EdgeOk(grammar, ids, q, w)

def edge_yes(ids, fuel, grammar, q, w, e):
  match ids:
    case Nil{}:
      +no = not_yes(Guard.rhsTri(fuel, grammar, q, w), e)
      d => rhs_no(fuel, grammar, q, w, no, d)
    case Con{+x, +rest}:
      none_derive_yes(x <> rest, fuel, grammar, w, e)

law edge_no:
  for ids: +List<Nat>
  for +fuel: Nat
  for +grammar: +List<Core.Production>
  for +q: Nat
  for +w: +List<Nat>
  for +e: {Guard.edgeTri(ids, fuel, grammar, q, w) == Guard.No{} : Guard.Tri}
  for h: Guard.EdgeOk(grammar, ids, q, w)
  Empty

def edge_no(ids, fuel, grammar, q, w, e, h):
  match ids:
    case Nil{}:
      h(rhs_yes(fuel, grammar, q, w, not_no(Guard.rhsTri(fuel, grammar, q, w), e)))
    case Con{+x, +rest}:
      none_derive_no(x <> rest, fuel, grammar, w, e, h)
