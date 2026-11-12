exec(open('common.py').read())
out = []
out.append('''import Base
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws
import ./GLL.bend as Gll
import ./LEMMAS.bend as Lemma
import ./PROOF_GLL.bend as G
import ./PROOF_ROUNDS.bend as R
import ./PROOF_PREFER.bend as Pf
import ./PROOF_LL1.bend as L
import ./PROOF_UNAMBIGUOUS.bend as U
import ./FITS.bend as Fits

# LL(1) AT ONE CHOICE POINT DECIDES IT. Walk one parse tree: every choice it makes (SPEC's
# choicesMade) predicts the token where it is made, by the same reasoning as in
# PROOF_UNAMBIGUOUS (FIRST when the chosen part reads something, else nullable and FOLLOW
# from the tree's own steps). Two trees choosing at one point and position, with the same
# token there, then choose the same, or LL1At at that point would be broken.

# ======== CHOICES THAT PREDICT ========

# The choice predicts the token where it is made.
def Ok(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, m: Spec.Made) -> Type:
  match m:
    case Spec.Made{+point, +pos, +choice}:
      Spec.ChoicePredicts(grammar, start, Spec.choiceOf(grammar, point, choice), List.get(&2, Nat, input, pos))

def AllOk(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, ms: +List<Spec.Made>) -> Type:
  match ms:
    case Nil{}:
      {0n == 0n : Nat}
    case Con{+m, rest}:
      Ok(grammar, start, input, m) & AllOk(grammar, start, input, rest)

law ok_append:
  for xs: +List<Spec.Made>
  for +ys: +List<Spec.Made>
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for hx: AllOk(grammar, start, input, xs)
  for hy: AllOk(grammar, start, input, ys)
  AllOk(grammar, start, input, List.append(&2, Spec.Made, xs, ys))

def ok_append(xs, ys, grammar, start, input, hx, hy):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      match hx:
        case (h, t):
          (h, ok_append(rest, ys, grammar, start, input, t, hy))

law among_ok:
  for xs: +List<Spec.Made>
  for +x: Spec.Made
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for am: Spec.Among(x, xs)
  for all: AllOk(grammar, start, input, xs)
  Ok(grammar, start, input, x)

def among_ok(xs, x, grammar, start, input, am, all):
  match xs:
    case Nil{}:
      Empty.absurd(Ok(grammar, start, input, x), am)
    case Con{+y, +rest}:
      match am:
        case Inl{e}:
          match all:
            case (h, t):
              +ye = Equal.sym(Spec.Made, x, y, e)
              %ye : Ok(grammar, start, input, _)
              h
        case Inr{later}:
          match all:
            case (h, t):
              among_ok(rest, x, grammar, start, input, later, t)

# What the walk knows of a forest. In a sequence: it fits the items from the dot, spells the
# input from k, and walks inside the root's steps. In the rounds of a loop (the bracket at
# the dot): rounds of its body from k that read as they must, ending at E, where leaving
# the loop predicts the token.
def Ready(rounds: Bool, +grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root: Spec.Tree, +f: +List<Spec.Tree>, +items: +List<Spec.Item>, +index: Nat, +prefix: +List<Nat>, +dot: Nat, +i: Nat, +k: Nat, +kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>, +restO: +List<Spec.Item>, +later: Bool, +E: Nat) -> Type:
  match rounds:
    case False{}:
      {Spec.fits(f, grammar, items) == True{} : Bool} & G.Spells(f, input, k) & {Spec.allIn(Spec.walk(f, False{}, index, prefix, dot, i, k), Spec.steps(root, 0n)) == True{} : Bool} &
        {Spec.itemsFrom(dot, Spec.sequenceAt(grammar, index, prefix)) == items : +List<Spec.Item>} & {L.evenLength(prefix) == True{} : Bool}
    case True{}:
      {Spec.itemAt(Spec.sequenceAt(grammar, index, prefix), dot) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>} & {Spec.itemsFrom(1n+dot, Spec.sequenceAt(grammar, index, prefix)) == restO : +List<Spec.Item>} &
        {Gll.isLoop(kind) == True{} : Bool} & {L.evenLength(prefix) == True{} : Bool} &
        {Spec.fits(f, grammar, Spec.times(List.length(&2, Spec.Tree, f), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool} & {U.roundsFine(kind, later, f) == True{} : Bool} &
        G.Spells(f, input, k) & {Spec.allIn(Spec.walk(f, True{}, index, List.append(&2, Nat, prefix, [dot]), 0n, i, k), Spec.steps(root, 0n)) == True{} : Bool} &
        {Nat.add(k, List.length(&2, Nat, Spec.leaves(f))) == E : Nat} & Spec.Predicts(grammar, start, restO, index, prefix, List.get(&2, Nat, input, E))

def IH(+grammar: +List<Spec.Production>, +start: Nat, +input: +List<Nat>, +root: Spec.Tree, +rootFit: {Spec.fits([root], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}, +rootSp: {Spec.leaves([root]) == input : +List<Nat>}, +f: +List<Spec.Tree>) -> Type:
  @rounds: Bool -> @later: Bool -> @items: +List<Spec.Item> -> @index: Nat -> @prefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> -> @restO: +List<Spec.Item> -> @E: Nat ->
    Ready(rounds, grammar, start, input, root, f, items, index, prefix, dot, i, k, kind, alts, restO, later, E) -> AllOk(grammar, start, input, Spec.madeIn(grammar, f, rounds, later, index, prefix, dot, k))
''')

ITEM_CASES = [('Nil{}', '[]'), ('Con{Spec.Sym{Spec.Terminal{t0}}, r0}', 'Spec.Sym{Spec.Terminal{t0}} <> r0'), ('Con{Spec.Sym{Spec.Nonterminal{x0}}, r0}', 'Spec.Sym{Spec.Nonterminal{x0}} <> r0'),
              ('Con{Spec.Brack{Spec.Group{}, b0}, r0}', 'Spec.Brack{Spec.Group{}, b0} <> r0'), ('Con{Spec.Brack{Spec.Optional{}, b0}, r0}', 'Spec.Brack{Spec.Optional{}, b0} <> r0'),
              ('Con{Spec.Brack{Spec.Closure{}, b0}, r0}', 'Spec.Brack{Spec.Closure{}, b0} <> r0'), ('Con{Spec.Brack{Spec.Positive{}, b0}, r0}', 'Spec.Brack{Spec.Positive{}, b0} <> r0'), ('Con{Spec.Eps{}, r0}', 'Spec.Eps{} <> r0')]
def absurd_cases(skip, F, goal):
    s = ''
    for pat, expr in ITEM_CASES:
        if pat.split('{')[0:3] and any(pat.startswith(p) for p in skip):
            continue
        s += '''    case %s:
      match ready:
        case (fit, rest):
          Empty.absurd(%s, Lemma.false_is_not_true(fit))
''' % (pat, goal)
    return s

# ---- a leaf ----
F = 'Spec.Leaf{a} <> ts'
G0 = allok(made(F))
s = '''
law leaf_ok:
  for items: +List<Spec.Item>
''' + TB + CTX + '''  for +a: Nat
  for +ts: +List<Spec.Tree>
  for ready: %(ready)s
  for ihTs: %(ih)s
  %(goal)s

def leaf_ok(items, %(tba)s, %(ctxa)s, a, ts, ready, ihTs):
  match items:
    case Con{Spec.Sym{Spec.Terminal{+term}}, +restI}:
      match ready:
%(bind)s          +itT = U.items_from_tail(dot, %(seq)s, Spec.Sym{Spec.Terminal{term}}, restI, itemsEq)
          ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, 1n+k, kind, alts, restO, E,
            %(rd)s)
''' % {'ready': ready('False{}', F), 'ih': ih('ts'), 'goal': G0, 'tba': TBA, 'ctxa': CTXA, 'seq': SEQ, 'bind': seq_bind(F, 'Spec.Sym{Spec.Terminal{term}} <> restI'),
       'rd': tup(['Fits.fits_tail(Spec.Leaf{a}, ts, grammar, Spec.Sym{Spec.Terminal{term}}, restI, fit)', 'G.leaf_rest(input, k, a, Spec.leaves(ts), sp)',
                  'U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, 1n+k), %s, %s, inW)' % (walkS('ts', '1n+dot', '1n+k'), STEPS), 'itT', 'even'])}
s += absurd_cases(['Con{Spec.Sym{Spec.Terminal'], F, G0)
out.append(s)

# ---- a skip ----
F = 'Spec.Skip{} <> ts'
G0 = allok(made(F))
TAIL = lambda it: '''U.items_from_tail(dot, %s, %s, restI, itemsEq)''' % (SEQ, it)
s = '''
law skip_ok:
  for items: +List<Spec.Item>
''' + TB + CTX + '''  for +ts: +List<Spec.Tree>
  for ready: %(ready)s
  for ihTs: %(ih)s
  %(goal)s

def skip_ok(items, %(tba)s, %(ctxa)s, ts, ready, ihTs):
  match items:
    case Con{Spec.Eps{}, +restI}:
      match ready:
%(bindE)s          +itT = %(tailE)s
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(%(seq)s, dot), Some{Spec.Eps{}}, U.items_from_head(dot, %(seq)s, Spec.Eps{}, restI, itemsEq))
          %%itS : AllOk(grammar, start, input, List.append(&2, Spec.Made, Spec.skipMade(_, index, prefix, dot, k), %(madeTs)s))
          ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, k, kind, alts, restO, E, %(rd)s)
    case Con{Spec.Brack{Spec.Optional{}, +balts}, +restI}:
      match ready:
%(bindB)s          +it = {Spec.Brack{Spec.Optional{}, balts} : Spec.Item}
          +itAt = U.items_from_head(dot, %(seq)s, it, restI, itemsEq)
          +itT = %(tailB)s
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(%(seq)s, dot), Some{it}, itAt)
          +next = List.get(&2, Nat, input, k)
          +n = List.length(&2, +List<Spec.Item>, balts)
          cpL = U.bracket_cp(grammar, start, index, prefix, dot, n, Spec.Optional{}, balts, restI, next, itAt, itT,
            U.leave_cp(Spec.isAlt(balts, n), grammar, start, balts, index, prefix, dot, False{}, True{}, restI, next, Pf.lt_irrefl(n), {==},
              U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ts, restI, index, prefix, prefix, k, i, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts))), %(walkF)s, Fits.fits_tail(Spec.Skip{}, ts, grammar, it, restI, fit), sp, {==}, {==}, {==},
                U.end_walk(Spec.Skip{} <> ts, it <> restI, dot, grammar, index, prefix, i, k, Nat.add(k, List.length(&2, Nat, Spec.leaves(ts))), fit, itemsEq, {==}, Lemma.or_true_right_intro(Nat.is_eq(dot, 0n), Bool.not(List.is_empty(&2, Spec.Tree, Spec.Skip{} <> ts)), {==})), inW)))
          %%itS : AllOk(grammar, start, input, List.append(&2, Spec.Made, Spec.skipMade(_, index, prefix, dot, k), %(madeTs)s))
          (cpL, ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, k, kind, alts, restO, E, %(rdB)s))
''' % {'ready': ready('False{}', F), 'ih': ih('ts'), 'goal': G0, 'tba': TBA, 'ctxa': CTXA, 'seq': SEQ,
       'bindE': seq_bind(F, 'Spec.Eps{} <> restI'), 'bindB': seq_bind(F, 'Spec.Brack{Spec.Optional{}, balts} <> restI'),
       'tailE': TAIL('Spec.Eps{}'), 'tailB': TAIL('it'), 'madeTs': made('ts', later='False{}', dot='1n+dot'),
       'walkF': walkS('Spec.Skip{} <> ts'),
       'rd': tup(['Fits.fits_tail(Spec.Skip{}, ts, grammar, Spec.Eps{}, restI, fit)', 'sp', 'U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), %s, %s, inW)' % (walkS('ts', '1n+dot'), STEPS), 'itT', 'even']),
       'rdB': tup(['Fits.fits_tail(Spec.Skip{}, ts, grammar, it, restI, fit)', 'sp', 'U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, k), %s, %s, inW)' % (walkS('ts', '1n+dot'), STEPS), 'itT', 'even'])}
s += absurd_cases(['Con{Spec.Eps', 'Con{Spec.Brack{Spec.Optional'], F, G0)
out.append(s)

# ---- a node ----
F = 'Spec.Node{q, ch} <> ts'
G0 = allok(made(F))
X = 'Spec.Sym{Spec.Nonterminal{x}}'
s = '''
law node_ok:
  for items: +List<Spec.Item>
''' + TB + CTX + '''  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for ready: %(ready)s
  for ihCh: %(ihc)s
  for ihTs: %(iht)s
  %(goal)s

def node_ok(items, %(tba)s, %(ctxa)s, q, ch, ts, ready, ihCh, ihTs):
  match items:
    case Con{Spec.Sym{Spec.Nonterminal{+x}}, +restI}:
      match ready:
%(bind)s          +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
          +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, restI), fit)
          +lhs = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fC = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
          +fT = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, restI), fit)
          +lc = Spec.leaves(ch)
          +lt = Spec.leaves(ts)
          +e = Nat.add(k, List.length(&2, Nat, lc))
          +spC = G.spells_first(input, k, lc, lt, sp)
          +spT = G.spells_second(input, k, lc, lt, sp)
          +wC = Spec.walk(ch, False{}, q, [], 0n, k, k)
          +wT = %(wT)s
          +inA = U.all_in_tail(Spec.at(index, prefix, 1n+dot, i, k, e), List.append(&2, Spec.Bsr, wC, wT), %(steps)s, inW)
          +inC = U.all_in_left(wC, wT, %(steps)s, inA)
          +inT = U.all_in_right(wC, wT, %(steps)s, inA)
          +itAt = U.items_from_head(dot, %(seq)s, %(X)s, restI, itemsEq)
          +itT = U.items_from_tail(dot, %(seq)s, %(X)s, restI, itemsEq)
          +itS = Equal.sym(Maybe<&2, Spec.Item>, Spec.itemAt(%(seq)s, dot), Some{%(X)s}, itAt)
          +next = List.get(&2, Nat, input, k)
          cp = U.nt_cp(Spec.lhsIs(grammar, q, x), grammar, start, q, next, lhs,
            U.predicts_in(next, grammar, start, input, root, rootFit, rootSp, ch, Spec.rhsOf(grammar, q), q, [], [], k, k, e, wC, fC, spC, {==}, {==}, {==},
              U.end_walk(ch, Spec.rhsOf(grammar, q), 0n, grammar, q, [], k, k, e, fC, {==}, {==}, {==}), inC))
          okC = ihCh(False{}, False{}, Spec.rhsOf(grammar, q), q, [], 0n, k, k, kind, alts, restO, E, %(rdC)s)
          okT = ihTs(False{}, False{}, restI, index, prefix, 1n+dot, i, e, kind, alts, restO, E, %(rdT)s)
          %%itS : AllOk(grammar, start, input, Spec.Made{Spec.NonterminalAt{Spec.nonterminalOf(_)}, k, q} <> List.append(&2, Spec.Made, %(mC)s, %(mT)s))
          (cp, ok_append(%(mC)s, %(mT)s, grammar, start, input, okC, okT))
''' % {'ready': ready('False{}', F), 'ihc': ih('ch'), 'iht': ih('ts'), 'goal': G0, 'tba': TBA, 'ctxa': CTXA, 'seq': SEQ, 'X': X, 'steps': STEPS, 'bind': seq_bind(F, X + ' <> restI'),
       'wT': walkS('ts', '1n+dot', 'e'), 'mC': made('ch', later='False{}', index='q', prefix='[]', dot='0n'), 'mT': made('ts', later='False{}', dot='1n+dot', k='e'),
       'rdC': tup(['fC', 'spC', 'inC', '{==}', '{==}']), 'rdT': tup(['fT', 'spT', 'inT', 'itT', 'even'])}
s += absurd_cases(['Con{Spec.Sym{Spec.Nonterminal'], F, G0)
out.append(s)
open('a.bend', 'w').write(''.join(out))
