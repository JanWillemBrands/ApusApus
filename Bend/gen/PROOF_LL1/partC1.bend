
# ======== EVERY CHOICE POINT IS CHECKED ========

# ---- Lists of conflicts that are not empty ----

law nonempty_left:
  for xs: +List<LL1.Conflict>
  for +ys: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, xs) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, ys)) == False{} : Bool}

def nonempty_left(xs, ys, h):
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, ys) == False{} : Bool}, Lemma.true_is_not_false(h))
    case Con{x, rest}:
      {==}

law nonempty_right:
  for xs: +List<LL1.Conflict>
  for +ys: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, ys) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, List.append(&2, LL1.Conflict, xs, ys)) == False{} : Bool}

def nonempty_right(xs, ys, h):
  match xs:
    case Nil{}:
      h
    case Con{x, rest}:
      {==}

law meet_pick_true:
  for meet: Bool
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +rest: +List<LL1.Conflict>
  for e: {meet == True{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.meetPick(meet, point, first, second, rest)) == False{} : Bool}

def meet_pick_true(meet, point, first, second, rest, e):
  match meet:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, rest) == False{} : Bool}, Lemma.false_is_not_true(e))

law meet_pick_rest:
  for meet: Bool
  for +point: Spec.ChoicePoint
  for +first: Nat
  for +second: Nat
  for +rest: +List<LL1.Conflict>
  for h: {List.is_empty(&2, LL1.Conflict, rest) == False{} : Bool}
  {List.is_empty(&2, LL1.Conflict, LL1.meetPick(meet, point, first, second, rest)) == False{} : Bool}

def meet_pick_rest(meet, point, first, second, rest, h):
  match meet:
    case True{}:
      {==}
    case False{}:
      h

# ---- Two sets that admit the same token meet ----

law in_nonempty:
  for +x: Nat
  for xs: +List<Nat>
  for h: {Gll.natIn(x, xs) == True{} : Bool}
  {Bool.not(List.is_empty(&2, Nat, xs)) == True{} : Bool}

def in_nonempty(x, xs, h):
  match xs:
    case Nil{}:
      Empty.absurd({Bool.not(List.is_empty(&2, Nat, [])) == True{} : Bool}, Lemma.false_is_not_true(h))
    case Con{y, rest}:
      {==}

law has_nonempty:
  for next: Maybe<&2, Nat>
  for s: Gll.LSet
  for h: {Gll.lsHas(next, s) == True{} : Bool}
  {LL1.lsNonEmpty(s) == True{} : Bool}

def has_nonempty(next, s, h):
  match next s:
    case None{} Gll.LSet{+any, +tokens, +end}:
      either_case({any == True{} : Bool}, {end == True{} : Bool}, {LL1.lsNonEmpty(Gll.LSet{any, tokens, end}) == True{} : Bool}, Lemma.or_true_cases(any, end, h),
        ea => Lemma.or_true_left_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), ea),
        ee => Lemma.or_true_right_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), Lemma.or_true_left_intro(end, Bool.not(List.is_empty(&2, Nat, tokens)), ee)))
    case Some{+tok} Gll.LSet{+any, +tokens, +end}:
      either_case({any == True{} : Bool}, {Gll.natIn(tok, tokens) == True{} : Bool}, {LL1.lsNonEmpty(Gll.LSet{any, tokens, end}) == True{} : Bool}, Lemma.or_true_cases(any, Gll.natIn(tok, tokens), h),
        ea => Lemma.or_true_left_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), ea),
        et => Lemma.or_true_right_intro(any, Bool.or(end, Bool.not(List.is_empty(&2, Nat, tokens))), Lemma.or_true_right_intro(end, Bool.not(List.is_empty(&2, Nat, tokens)), in_nonempty(tok, tokens, et))))

law tokens_meet:
  for +tok: Nat
  for xs: +List<Nat>
  for +ys: +List<Nat>
  for hx: {Gll.natIn(tok, xs) == True{} : Bool}
  for +hy: {Gll.natIn(tok, ys) == True{} : Bool}
  {LL1.tokensMeet(xs, ys) == True{} : Bool}

def tokens_meet(tok, xs, ys, hx, hy):
  match xs:
    case Nil{}:
      Empty.absurd({LL1.tokensMeet([], ys) == True{} : Bool}, Lemma.false_is_not_true(hx))
    case Con{+x, +rest}:
      either_case({Nat.is_eq(tok, x) == True{} : Bool}, {Gll.natIn(tok, rest) == True{} : Bool}, {LL1.tokensMeet(x <> rest, ys) == True{} : Bool}, Lemma.or_true_cases(Nat.is_eq(tok, x), Gll.natIn(tok, rest), hx),
        here => Lemma.or_true_left_intro(Gll.natIn(x, ys), LL1.tokensMeet(rest, ys),
          Equal.trans(Bool, Gll.natIn(x, ys), Gll.natIn(tok, ys), True{}, Equal.cong(Nat, Bool, v => Gll.natIn(v, ys), x, tok, Equal.sym(Nat, tok, x, Lemma.nat_eq_sound(tok, x, here))), hy)),
        later => Lemma.or_true_right_intro(Gll.natIn(x, ys), LL1.tokensMeet(rest, ys), tokens_meet(tok, rest, ys, later, hy)))

law meet_of_has:
  for next: Maybe<&2, Nat>
  for a: Gll.LSet
  for b: Gll.LSet
  for +ha: {Gll.lsHas(next, a) == True{} : Bool}
  for +hb: {Gll.lsHas(next, b) == True{} : Bool}
  {LL1.lsMeet(a, b) == True{} : Bool}

def meet_of_has(next, a, b, ha, hb):
  match next a b:
    case None{} Gll.LSet{+a1, +t1, +e1} Gll.LSet{+a2, +t2, +e2}:
      +sa = {Gll.LSet{a1, t1, e1} : Gll.LSet}
      +sb = {Gll.LSet{a2, t2, e2} : Gll.LSet}
      +m1 = Bool.and(a1, LL1.lsNonEmpty(sb))
      +m2 = Bool.and(a2, LL1.lsNonEmpty(sa))
      +m3 = Bool.and(e1, e2)
      +m4 = LL1.tokensMeet(t1, t2)
      either_case({a1 == True{} : Bool}, {e1 == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a1, e1, ha),
        any1 => Lemma.or_true_left_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.and_true_intro(a1, LL1.lsNonEmpty(sb), any1, has_nonempty(None{}, sb, hb))),
        end1 => either_case({a2 == True{} : Bool}, {e2 == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a2, e2, hb),
          any2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_left_intro(m2, Bool.or(m3, m4), Lemma.and_true_intro(a2, LL1.lsNonEmpty(sa), any2, has_nonempty(None{}, sa, ha)))),
          end2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_right_intro(m2, Bool.or(m3, m4), Lemma.or_true_left_intro(m3, m4, Lemma.and_true_intro(e1, e2, end1, end2))))))
    case Some{+tok} Gll.LSet{+a1, +t1, +e1} Gll.LSet{+a2, +t2, +e2}:
      +sa = {Gll.LSet{a1, t1, e1} : Gll.LSet}
      +sb = {Gll.LSet{a2, t2, e2} : Gll.LSet}
      +m1 = Bool.and(a1, LL1.lsNonEmpty(sb))
      +m2 = Bool.and(a2, LL1.lsNonEmpty(sa))
      +m3 = Bool.and(e1, e2)
      +m4 = LL1.tokensMeet(t1, t2)
      either_case({a1 == True{} : Bool}, {Gll.natIn(tok, t1) == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a1, Gll.natIn(tok, t1), ha),
        any1 => Lemma.or_true_left_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.and_true_intro(a1, LL1.lsNonEmpty(sb), any1, has_nonempty(Some{tok}, sb, hb))),
        in1 => either_case({a2 == True{} : Bool}, {Gll.natIn(tok, t2) == True{} : Bool}, {Bool.or(m1, Bool.or(m2, Bool.or(m3, m4))) == True{} : Bool}, Lemma.or_true_cases(a2, Gll.natIn(tok, t2), hb),
          any2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_left_intro(m2, Bool.or(m3, m4), Lemma.and_true_intro(a2, LL1.lsNonEmpty(sa), any2, has_nonempty(Some{tok}, sa, ha)))),
          in2 => Lemma.or_true_right_intro(m1, Bool.or(m2, Bool.or(m3, m4)), Lemma.or_true_right_intro(m2, Bool.or(m3, m4), Lemma.or_true_right_intro(m3, m4, tokens_meet(tok, t1, t2, in1, in2))))))

# ---- A choice in a list, with a set that admits the token ----

def HasAt(+c: Nat, +next: Maybe<&2, Nat>, xs: +List<LL1.Predicted>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{LL1.Predicted{c2, s2}, rest}:
      Either<({c == c2 : Nat} & {Gll.lsHas(next, s2) == True{} : Bool}), HasAt(c, next, rest)>

law has_append_left:
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for xs: +List<LL1.Predicted>
  for +ys: +List<LL1.Predicted>
  for h: HasAt(c, next, xs)
  HasAt(c, next, List.append(&2, LL1.Predicted, xs, ys))

def has_append_left(c, next, xs, ys, h):
  match xs:
    case Nil{}:
      Empty.absurd(HasAt(c, next, ys), h)
    case Con{LL1.Predicted{+c2, +s2}, +rest}:
      match h:
        case Inl{here}:
          Inl{here}
        case Inr{later}:
          Inr{has_append_left(c, next, rest, ys, later)}

law has_append_right:
  for +c: Nat
  for +next: Maybe<&2, Nat>
  for xs: +List<LL1.Predicted>
  for +ys: +List<LL1.Predicted>
  for h: HasAt(c, next, ys)
  HasAt(c, next, List.append(&2, LL1.Predicted, xs, ys))

def has_append_right(c, next, xs, ys, h):
  match xs:
    case Nil{}:
      h
    case Con{LL1.Predicted{+c2, +s2}, +rest}:
      Inr{has_append_right(c, next, rest, ys, h)}

# One choice against the choices after it.
law with_hit:
  for +point: Spec.ChoicePoint
  for +c: Nat
  for +s: Gll.LSet
  for rest: +List<LL1.Predicted>
  for +next: Maybe<&2, Nat>
  for +c2: Nat
  for +hs: {Gll.lsHas(next, s) == True{} : Bool}
  for h: HasAt(c2, next, rest)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsWith(point, LL1.Predicted{c, s}, rest)) == False{} : Bool}

def with_hit(point, c, s, rest, next, c2, hs, h):
  match rest:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.conflictsWith(point, LL1.Predicted{c, s}, [])) == False{} : Bool}, h)
    case Con{LL1.Predicted{+c3, +s3}, +r}:
      match h:
        case Inl{here}:
          match here:
            case (eq, hs3):
              meet_pick_true(LL1.lsMeet(s, s3), point, c, c3, LL1.conflictsWith(point, LL1.Predicted{c, s}, r), meet_of_has(next, s, s3, hs, hs3))
        case Inr{later}:
          meet_pick_rest(LL1.lsMeet(s, s3), point, c, c3, LL1.conflictsWith(point, LL1.Predicted{c, s}, r), with_hit(point, c, s, r, next, c2, hs, later))

# Two different choices in the list, both admitting the token: a conflict.
law among_hit:
  for +point: Spec.ChoicePoint
  for xs: +List<LL1.Predicted>
  for +c1: Nat
  for +c2: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(c1, c2) == False{} : Bool}
  for h1: HasAt(c1, next, xs)
  for h2: HasAt(c2, next, xs)
  {List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(point, xs)) == False{} : Bool}

def among_hit(point, xs, c1, c2, next, neq, h1, h2):
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(point, [])) == False{} : Bool}, h1)
    case Con{LL1.Predicted{+c, +s}, +rest}:
      match h1:
        case Inl{here1}:
          match here1:
            case (e1, hs1):
              match h2:
                case Inl{here2}:
                  match here2:
                    case (e2, hs2):
                      Empty.absurd({List.is_empty(&2, LL1.Conflict, LL1.conflictsAmong(point, LL1.Predicted{c, s} <> rest)) == False{} : Bool}, Lemma.false_is_not_true(Equal.trans(Bool, False{}, Nat.is_eq(c1, c2), True{}, Equal.sym(Bool, Nat.is_eq(c1, c2), False{}, neq),
                        Lemma.nat_eq_of_eq(c1, c2, Equal.trans(Nat, c1, c, c2, e1, Equal.sym(Nat, c2, c, e2))))))
                case Inr{later2}:
                  nonempty_left(LL1.conflictsWith(point, LL1.Predicted{c, s}, rest), LL1.conflictsAmong(point, rest), with_hit(point, c, s, rest, next, c2, hs1, later2))
        case Inr{later1}:
          match h2:
            case Inl{here2}:
              match here2:
                case (e2, hs2):
                  nonempty_left(LL1.conflictsWith(point, LL1.Predicted{c, s}, rest), LL1.conflictsAmong(point, rest), with_hit(point, c, s, rest, next, c1, hs2, later1))
            case Inr{later2}:
              nonempty_right(LL1.conflictsWith(point, LL1.Predicted{c, s}, rest), LL1.conflictsAmong(point, rest), among_hit(point, rest, c1, c2, next, neq, later1, later2))
