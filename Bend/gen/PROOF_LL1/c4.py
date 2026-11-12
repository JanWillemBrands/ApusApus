KINDS = [('Group', 'True{}', 'False{}'), ('Optional', 'False{}', 'True{}'), ('Closure', 'False{}', 'True{}'), ('Positive', 'True{}', 'False{}')]
FIXD = '''  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +index: Nat
  for +p: +List<Nat>
  for +dot: Nat
  for +rest: +List<Spec.Item>
  for +first: Nat
  for +second: Nat
  for +next: Maybe<&2, Nat>
  for +neq: {Nat.is_eq(first, second) == False{} : Bool}
'''
FIX = 'grammar, start, t, po, index, p, dot, rest, first, second, next, neq'
SEQ = 'Spec.sequenceAt(grammar, index, p)'
R = 'Gll.reverseOnto(p, [])'
def law(name, afterRound):
    ar = 'True{}' if afterRound else 'False{}'
    s = 'law %s:\n  for it: Maybe<&2, Spec.Item>\n' % name + FIXD
    s += '  for itS: {Spec.itemAt(%s, dot) == it : Maybe<&2, Spec.Item>}\n' % SEQ
    s += '  for +restS: {rest == Spec.itemsFrom(1n+dot, %s) : +List<Spec.Item>}\n' % SEQ
    s += '  for cp1: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(it, %s, first, index, p, dot, rest), next)\n' % ar
    s += '  for cp2: Spec.ChoicePredicts(grammar, start, Spec.bracketChoice(it, %s, second, index, p, dot, rest), next)\n' % ar
    s += '  {List.is_empty(&2, LL1.Conflict, localConflicts(it, grammar, t, index, %s, dot)) == False{} : Bool}\n\n' % R
    s += 'def %s(it, %s, itS, restS, cp1, cp2):\n  match it:\n' % (name, FIX)
    GOAL = lambda it: '{List.is_empty(&2, LL1.Conflict, localConflicts(%s, grammar, t, index, %s, dot)) == False{} : Bool}' % (it, R)
    s += '    case None{}:\n      Empty.absurd(%s, cp1)\n' % GOAL('None{}')
    s += '    case Some{Spec.Sym{sym}}:\n      Empty.absurd(%s, cp1)\n' % GOAL('Some{Spec.Sym{sym}}')
    s += '    case Some{Spec.Eps{}}:\n      Empty.absurd(%s, cp1)\n' % GOAL('Some{Spec.Eps{}}')
    for k, mbe, leave in KINDS:
        it = 'Some{Spec.Brack{Spec.%s{}, alts}}' % k
        kind = 'Spec.%s{}' % k
        s += '    case Some{Spec.Brack{Spec.%s{}, +alts}}:\n' % k
        if afterRound and k != 'Positive':
            s += '      Empty.absurd(%s, cp1)\n' % GOAL(it)
            continue
        if afterRound:
            mbe, leave = 'False{}', 'True{}'
        s += '''      +R = %s
      +rEq = reverse_twice(p, [])
      +itS1 = {itS : {Spec.itemAt(%s, dot) == %s : Maybe<&2, Spec.Item>}}
      +seqEq = seq_path(p, [], grammar, index, dot, Spec.Brack{%s, alts}, itS1)
      +itEq = Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(Gll.seqAt(grammar, index, R), dot), Gll.nthItem(%s, dot), %s,
        Equal.cong(+List<Spec.Item>, Maybe<&2, Spec.Item>, v => Gll.nthItem(v, dot), Gll.seqAt(grammar, index, R), %s, Equal.sym(+List<Spec.Item>, %s, Gll.seqAt(grammar, index, R), seqEq)),
        Equal.trans(Maybe<&2, Spec.Item>, Gll.nthItem(%s, dot), Spec.itemAt(%s, dot), %s, Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(%s, dot), Gll.nthItem(%s, dot), item_at_eq(%s, dot)), itS1))
      +restEq = Equal.trans(+List<Spec.Item>, rest, Spec.itemsFrom(1n+dot, %s), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), restS,
        Equal.trans(+List<Spec.Item>, Spec.itemsFrom(1n+dot, %s), Gll.dropFrom(1n+dot, %s), Gll.dropFrom(1n+dot, Gll.seqAt(grammar, index, R)), items_from_eq(1n+dot, %s),
          Equal.cong(+List<Spec.Item>, +List<Spec.Item>, v => Gll.dropFrom(1n+dot, v), %s, Gll.seqAt(grammar, index, R), seqEq)))
      h1 = alt_choice(Spec.isAlt(alts, first), grammar, start, t, po, %s, alts, first, index, p, R, dot, %s, %s, rest, next, {==}, rEq, itEq, restEq, cp1)
      h2 = alt_choice(Spec.isAlt(alts, second), grammar, start, t, po, %s, alts, second, index, p, R, dot, %s, %s, rest, next, {==}, rEq, itEq, restEq, cp2)
''' % (R, SEQ, it, kind, SEQ, it, SEQ, SEQ, SEQ, SEQ, it, SEQ, SEQ, SEQ, SEQ, SEQ, SEQ, SEQ, SEQ, kind, mbe, leave, kind, mbe, leave)
        enter = 'LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.enterChoices(%s, grammar, t, index, R, dot, alts))' % kind
        after = 'LL1.afterRoundConflicts(%s, grammar, t, index, R, dot, alts)' % kind
        if afterRound:
            s += '      nonempty_right(%s, %s, among_hit(Spec.AfterRoundAt{index, Gll.reverseOnto(R, []), dot}, LL1.choicesWith(False{}, True{}, grammar, t, index, R, dot, alts), first, second, next, neq, h1, h2))\n' % (enter, after)
        else:
            s += '      nonempty_left(%s, %s, among_hit(Spec.BracketAt{index, Gll.reverseOnto(R, []), dot}, LL1.choicesWith(%s, %s, grammar, t, index, R, dot, alts), first, second, next, neq, h1, h2))\n' % (enter, after, mbe, leave)
    return s

out = ['''
# The checks the table check makes at one item: entering it and, for < >, after a round.
def localConflicts(item: Maybe<&2, Spec.Item>, +grammar: +List<Spec.Production>, +t: Gll.Tables, +index: Nat, +rpath: +List<Nat>, +dot: Nat) -> +List<LL1.Conflict>:
  match item:
    case Some{Spec.Brack{+kind, +inner}}:
      List.append(&2, LL1.Conflict, LL1.conflictsAmong(Spec.BracketAt{index, Gll.reverseOnto(rpath, []), dot}, LL1.enterChoices(kind, grammar, t, index, rpath, dot, inner)), LL1.afterRoundConflicts(kind, grammar, t, index, rpath, dot, inner))
    case Some{Spec.Sym{s}}:
      []
    case Some{Spec.Eps{}}:
      []
    case None{}:
      []

# Two choices entering a bracket that predict the same token: a conflict there.
''', law('enter_local', False), '''
# Two choices after a round of < > that predict the same token: a conflict there.
''', law('after_local', True)]
open('partC4.bend', 'w').write(''.join(out))
