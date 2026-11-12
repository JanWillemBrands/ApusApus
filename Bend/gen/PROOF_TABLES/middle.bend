
# ---- FIRST IS SOUND: the first token a fitting forest reads is in FIRST ----

def tailOf(l: +List<Nat>) -> +List<Nat>:
  match l:
    case Nil{}:
      []
    case Con{h, t}:
      t

law cons_head_eq:
  for -h: Nat
  for -t: +List<Nat>
  for -k0: Nat
  for -w: +List<Nat>
  for e: {h <> t == k0 <> w : +List<Nat>}
  {h == k0 : Nat}

def cons_head_eq(h, t, k0, w, e):
  Equal.cong(+List<Nat>, Nat, l => Lemma.headOr(l, 0n), h <> t, k0 <> w, e)

law first_split:
  for lc: +List<Nat>
  for +lt: +List<Nat>
  for +k0: Nat
  for +w: +List<Nat>
  for -G: Type
  for lv: {List.append(&2, Nat, lc, lt) == k0 <> w : +List<Nat>}
  for here: {lc == k0 <> tailOf(lc) : +List<Nat>} -> G
  for later: {lc == [] : +List<Nat>} -> {lt == k0 <> w : +List<Nat>} -> G
  G

def first_split(lc, lt, k0, w, G, lv, here, later):
  match lc:
    case Nil{}:
      later({==}, lv)
    case Con{+h, +r}:
      +eh = cons_head_eq(h, List.append(&2, Nat, r, lt), k0, w, lv)
      here(Equal.cong(Nat, +List<Nat>, v => v <> r, h, k0, eh))

# The alternatives start with what the chosen one starts with, at any nesting fuel.
law alts_first_of:
  for f: Nat
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +t: Gll.Tables
  for +tok: Maybe<&2, Nat>
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for ih: @g: Nat -> {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(g, Gll.MItems{}, Spec.altOf(alts, a), [], t))) == True{} : Bool}
  {Gll.lsHas(tok, Gll.firstOf(Gll.infoOf(f, Gll.MAlts{}, [], alts, t))) == True{} : Bool}

def alts_first_of(f, alts, a, t, tok, isA, ih):
  match f:
    case 0n:
      Sets.any_has(tok, True{}, [], True{}, {==})
    case 1n+(+g):
      alt_first(alts, a, g, t, tok, isA, ih(g))

