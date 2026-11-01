import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./LEMMAS.bend as Lemma

# LOCALITY: the phases judge a node by what it reads (LAWS.bend, LOCALITY).

law hold_local:
  for g: Spec.Guard
  for +grammar: +List<Spec.Production>
  for +items: +List<Spec.Item>
  for +f: +List<Spec.Tree>
  for +f2: +List<Spec.Tree>
  for +ahead: +List<Nat>
  for +eF: {Spec.firstSpell(f2) == Spec.firstSpell(f) : Maybe<&2, +List<Nat>>}
  for +eL: {Spec.lastSpell(f2) == Spec.lastSpell(f) : Maybe<&2, +List<Nat>>}
  for h: Spec.Holds(grammar, g, items, f, ahead)
  Spec.Holds(grammar, g, items, f2, ahead)

def hold_local(g, grammar, items, f, f2, ahead, eF, eL, h):
  match g:
    case Spec.Ahead{ids}:
      h
    case Spec.NotAhead{ids}:
      h
    case Spec.LeftAssoc{+ids}:
      %Equal.sym(Maybe<&2, +List<Nat>>, Spec.lastSpell(f2), Spec.lastSpell(f), eL) : Spec.EdgeFree(grammar, ids, items, _)
      h
    case Spec.RightAssoc{+ids}:
      %Equal.sym(Maybe<&2, +List<Nat>>, Spec.firstSpell(f2), Spec.firstSpell(f), eF) : Spec.EdgeFree(grammar, ids, items, _)
      h

def Laws.holds_local(grammar, gs, items, f, f2, ahead, eF, eL, h):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, rest}:
      match h:
        case (hg, hr):
          (hold_local(g, grammar, items, f, f2, ahead, eF, eL, hg), Laws.holds_local(grammar, rest, items, f, f2, ahead, eF, eL, hr))

law last_swap:
  for ts: +List<Spec.Tree>
  for +t: Spec.Tree
  for +t2: Spec.Tree
  for +lv: {Spec.leaves([t2]) == Spec.leaves([t]) : +List<Nat>}
  {Spec.leaves([Spec.lastOf(ts, t2)]) == Spec.leaves([Spec.lastOf(ts, t)]) : +List<Nat>}

def last_swap(ts, t, t2, lv):
  match ts:
    case Nil{}:
      lv
    case Con{+u, +us}:
      {==}

def Laws.spells_swap(t, t2, ts, lv):
  (Equal.cong(+List<Nat>, Maybe<&2, +List<Nat>>, v => Some{v}, Spec.leaves([t2]), Spec.leaves([t]), lv),
    Equal.cong(+List<Nat>, Maybe<&2, +List<Nat>>, v => Some{v}, Spec.leaves([Spec.lastOf(ts, t2)]), Spec.leaves([Spec.lastOf(ts, t)]), last_swap(ts, t, t2, lv)))

def Laws.measures_swap(marks, t, t2, ts, items, index, prefix, dot, lv):
  match items:
    case Nil{}:
      {==}
    case Con{+it, +rest}:
      +r = Spec.measures(marks, ts, rest, index, prefix, 1n+dot)
      +ex = Spec.itemExtent(marks, it, index, List.append(&2, Nat, prefix, [dot]))
      Equal.cong(+List<Nat>, +List<Spec.Measure>, v => Spec.measureIf(ex, List.length(&2, Nat, v), r), Spec.leaves([t2]), Spec.leaves([t]), lv)

def Laws.admissible_swap_node(grammar, guards, q, ch, ch2, ts, x, rest, index, prefix, dot, after, lv, hold2, adm2, adm):
  match adm:
    case (hold, (admCh, admTs)):
      (hold2, (adm2, admTs))

def Laws.admissible_swap_pick(grammar, guards, a, ch, ch2, ts, kind, alts, rest, index, prefix, dot, after, lv, hold2, adm2, adm):
  match kind:
    case Spec.Group{}:
      match adm:
        case (hold, (admCh, admTs)):
          (hold2, (adm2, admTs))
    case Spec.Optional{}:
      match adm:
        case (hold, (admCh, admTs)):
          (hold2, (adm2, admTs))
    case Spec.Closure{}:
      match adm:
        case (hold, (admCh, admTs)):
          (hold2, (adm2, admTs))
    case Spec.Positive{}:
      match adm:
        case (hold, (admCh, admTs)):
          (hold2, (adm2, admTs))

law rival_swap_node:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +x: Nat
  for +q: Nat
  for +w: +List<Nat>
  for +w2: +List<Nat>
  for +next: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +lv: {w2 == w : +List<Nat>}
  for nr: Spec.ProdRival(grammar, guards, marks, x, q, w, next, x <> Spec.sameAbove(above, span, w)) -> Empty
  Spec.ProdRival(grammar, guards, marks, x, q, w2, next, x <> Spec.sameAbove(above, span, w2)) -> Empty

def rival_swap_node(grammar, guards, marks, x, q, w, w2, next, above, span, lv, nr):
  %Equal.sym(+List<Nat>, w2, w, lv) : Spec.ProdRival(grammar, guards, marks, x, q, _, next, x <> Spec.sameAbove(above, span, _)) -> Empty
  nr

law unb_swap_node:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +x: Nat
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +next: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for unb2: Spec.Unbeaten(grammar, guards, marks, ch2, Spec.rhsOf(grammar, q), q, [], 0n, x <> Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), next)
  Spec.Unbeaten(grammar, guards, marks, ch2, Spec.rhsOf(grammar, q), q, [], 0n, x <> Spec.sameAbove(above, span, Spec.leaves(ch2)), Spec.leaves(ch2), next)

def unb_swap_node(grammar, guards, marks, q, ch, ch2, x, above, span, next, lv, unb2):
  %Equal.sym(+List<Nat>, Spec.leaves(ch2), Spec.leaves(ch), lv) : Spec.Unbeaten(grammar, guards, marks, ch2, Spec.rhsOf(grammar, q), q, [], 0n, x <> Spec.sameAbove(above, span, _), _, next)
  unb2

def Laws.unbeaten_swap_node(grammar, guards, marks, q, ch, ch2, ts, x, rest, index, prefix, dot, above, span, after, lv, unb2, unb):
  match unb:
    case (nr, (unbCh, unbTs)):
      +next = List.append(&2, Nat, Spec.leaves(ts), after)
      (rival_swap_node(grammar, guards, marks, x, q, Spec.leaves(ch), Spec.leaves(ch2), next, above, span, lv, nr),
        (unb_swap_node(grammar, guards, marks, q, ch, ch2, x, above, span, next, lv, unb2), unbTs))

law rival_swap_pick:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +alts: +List<+List<Spec.Item>>
  for +index: Nat
  for +path: +List<Nat>
  for +a: Nat
  for +w: +List<Nat>
  for +w2: +List<Nat>
  for +next: +List<Nat>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +lv: {w2 == w : +List<Nat>}
  for nr: Spec.AltRival(grammar, guards, marks, alts, index, path, a, w, next, Spec.lhsOf(grammar, index) <> Spec.sameAbove(above, span, w)) -> Empty
  Spec.AltRival(grammar, guards, marks, alts, index, path, a, w2, next, Spec.lhsOf(grammar, index) <> Spec.sameAbove(above, span, w2)) -> Empty

def rival_swap_pick(grammar, guards, marks, alts, index, path, a, w, w2, next, above, span, lv, nr):
  %Equal.sym(+List<Nat>, w2, w, lv) : Spec.AltRival(grammar, guards, marks, alts, index, path, a, _, next, Spec.lhsOf(grammar, index) <> Spec.sameAbove(above, span, _)) -> Empty
  nr

law unb_swap_pick:
  for +grammar: +List<Spec.Production>
  for +guards: +List<Spec.GuardMark>
  for +marks: +List<Spec.Mark>
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +index: Nat
  for +pre: +List<Nat>
  for +ch: +List<Spec.Tree>
  for +ch2: +List<Spec.Tree>
  for +above: +List<Nat>
  for +span: +List<Nat>
  for +next: +List<Nat>
  for +lv: {Spec.leaves(ch2) == Spec.leaves(ch) : +List<Nat>}
  for unb2: Spec.Unbeaten(grammar, guards, marks, ch2, Spec.altOf(alts, a), index, pre, 0n, Spec.sameAbove(above, span, Spec.leaves(ch)), Spec.leaves(ch), next)
  Spec.Unbeaten(grammar, guards, marks, ch2, Spec.altOf(alts, a), index, pre, 0n, Spec.sameAbove(above, span, Spec.leaves(ch2)), Spec.leaves(ch2), next)

def unb_swap_pick(grammar, guards, marks, alts, a, index, pre, ch, ch2, above, span, next, lv, unb2):
  %Equal.sym(+List<Nat>, Spec.leaves(ch2), Spec.leaves(ch), lv) : Spec.Unbeaten(grammar, guards, marks, ch2, Spec.altOf(alts, a), index, pre, 0n, Spec.sameAbove(above, span, _), _, next)
  unb2

def Laws.unbeaten_swap_pick(grammar, guards, marks, a, ch, ch2, ts, kind, alts, rest, index, prefix, dot, above, span, after, lv, unb2, unb):
  match unb:
    case (nr, (unbCh, unbTs)):
      +next = List.append(&2, Nat, Spec.leaves(ts), after)
      +path = List.append(&2, Nat, prefix, [dot])
      +pre = List.append(&2, Nat, path, [a])
      (rival_swap_pick(grammar, guards, marks, alts, index, path, a, Spec.leaves(ch), Spec.leaves(ch2), next, above, span, lv, nr),
        (unb_swap_pick(grammar, guards, marks, alts, a, index, pre, ch, ch2, above, span, next, lv, unb2), unbTs))
