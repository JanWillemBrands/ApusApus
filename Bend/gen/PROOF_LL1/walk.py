# Generates the follow walk of PROOF_LL1.bend (appended after end_hit).
FIXD = '''  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +po: {Pr.predOk(Gll.Predict{t}, grammar, start) == True{} : Bool}
  for +input: +List<Nat>
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
'''
FIX = 'grammar, start, t, po, input, index0, prefix0, i0, k0, j0, rpath1, rEq'
TGT = 'index0, prefix0, i0, k0, j0, rpath1'
TARGET = 'target(grammar, index0, prefix0, i0, k0, j0)'
GOAL = 'Fits(grammar, t, input, index0, rpath1, j0)'
POSD = '''  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
'''
POS = 'index, rpath, prefix, seqPrefix, dot, i, k, ff, fin'
SEQ = 'Gll.seqAt(grammar, index, rpath)'
SEQD = '''  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(FOREST))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foF: {Pr.foOk(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +even: {evenLength(prefix) == True{} : Bool}
  for +seqEq: {Spec.sequenceAt(grammar, index, prefix) == Gll.seqAt(grammar, index, rpath) : +List<Spec.Item>}
'''
SEQA = 'pEq, finEq, ctxF, foF, even, seqEq'
def ih(name):
    return '  for %s: FollowIH(grammar, t, input, FOREST, %s)\n' % (name, TGT)
def hitd(forest, rounds='False{}'):
    return '  for +hit: {Spec.bsrMember(%s, Spec.walk(%s, %s, index, prefix, dot, i, k)) == True{} : Bool}\n' % (TARGET, forest, rounds)
def fitdrop(ts):
    return ('Equal.trans(Bool, Spec.fits(%s, grammar, G.dropItems(1n+dot, %s)), Spec.fits(%s, grammar, rest), True{}, '
            'Equal.cong(+List<Spec.Item>, Bool, v => Spec.fits(%s, grammar, v), G.dropItems(1n+dot, %s), rest, restEq), fitTs)') % (ts, SEQ, ts, ts, SEQ)
def call_ih(f, rounds, items, index, rpath, prefix, seqp, dot, i, k, ff, fin, kind, alts, pEq, sp, ready, hit):
    return '%s(%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)' % (f, rounds, index, rpath, prefix, seqp, dot, i, k, ff, fin, items, kind, alts, pEq, sp, ready, hit)
def seqready(rem, fit, fin, ctx, fo, even, seq):
    return '(%s, (%s, (%s, (%s, (%s, (%s, %s))))))' % (rem, fit, fin, ctx, fo, even, seq)
def either(a, b, cases, left, right, ind='  '):
    return '%seither_case(%s, %s, %s, %s,\n%s  %s,\n%s  %s)' % (ind, a, b, GOAL, cases, ind, left, ind, right)
def head_cases(here, tail, onHead, onTail, ind='  '):
    return either('{%s == %s : Spec.Bsr}' % (TARGET, here), '{Spec.bsrMember(%s, %s) == True{} : Bool}' % (TARGET, tail),
                  'G.ebnf_member_cases(%s, %s, %s, hit)' % (TARGET, here, tail), 'same => ' + onHead, 'there => ' + onTail, ind)
def split_cases(a, b, onA, onB, ind='      '):
    return either('{Spec.bsrMember(%s, %s) == True{} : Bool}' % (TARGET, a), '{Spec.bsrMember(%s, %s) == True{} : Bool}' % (TARGET, b),
                  'member_split(%s, %s, %s, there)' % (a, b, TARGET), 'inA => ' + onA, 'inB => ' + onB, ind)
def end_hit(e, ts, finTs):
    return 'end_hit(grammar, t, input, index, rpath, prefix, dot, i, k, %s, %s, rest, fin, %s, same, restEq, fitTs, %s, seqEq, pEq, ctxF, rEq)' % (e, ts, TGT, finTs)

out = []
out.append('''
# ======== THE FOLLOW WALK ========
#
# Walk a parse tree as SPEC.bend's `walk` does, with the invariants of PROOF_PRED in
# prediction mode. Wherever the walk lists the end step of a sequence (the target), the token
# there is in the tables' context for that sequence.

def target(+grammar: +List<Spec.Production>, +index0: Nat, +prefix0: +List<Nat>, +i0: Nat, +k0: Nat, +j0: Nat) -> Spec.Bsr:
  Spec.at(index0, prefix0, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0)), i0, k0, j0)

def FollowIH(+grammar: +List<Spec.Production>, +t: Gll.Tables, +input: +List<Nat>, +forest: +List<Spec.Tree>, +index0: Nat, +prefix0: +List<Nat>, +i0: Nat, +k0: Nat, +j0: Nat, +rpath1: +List<Nat>) -> Type:
  @rounds: Bool -> @index: Nat -> @rpath: +List<Nat> -> @prefix: +List<Nat> -> @seqPrefix: +List<Nat> -> @dot: Nat -> @i: Nat -> @k: Nat -> @ff: Nat -> @fin: Nat -> @items: +List<Spec.Item> -> @kind: Spec.Bracket -> @alts: +List<+List<Spec.Item>> ->
    {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>} -> G.Spells(forest, input, k) -> Ready(rounds, grammar, t, input, forest, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts) ->
    {Spec.bsrMember(target(grammar, index0, prefix0, i0, k0, j0), Spec.walk(forest, rounds, index, prefix, dot, i, k)) == True{} : Bool} -> Fits(grammar, t, input, index0, rpath1, j0)

# ---- The end of a sequence: only dot 0 has a step there ----

law empty_follow:
  for dot: Nat
''' + FIXD.replace('  for +grammar', '  for +grammar', 1) + '''  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +i: Nat
  for +k: Nat
  for +fin: Nat
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves([]))) == fin : Nat}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +hit: {Spec.bsrMember(%s, Spec.emptyStep(dot, index, prefix, i, k)) == True{} : Bool}
  %s

def empty_follow(dot, %s, index, rpath, prefix, i, k, fin, pEq, finEq, ctxF, hit):
  match dot:
    case 0n:
''' % (TARGET, GOAL, FIX))
here0 = 'Spec.at(index, prefix, 0n, i, k, k)'
out.append(either('{%s == %s : Spec.Bsr}' % (TARGET, here0), '{Spec.bsrMember(%s, []) == True{} : Bool}' % TARGET,
    'G.ebnf_member_cases(%s, %s, [], hit)' % (TARGET, here0),
    'same => at_fits(grammar, t, input, index, rpath, prefix, 0n, i, k, k, fin, %s, same, Equal.trans(Nat, k, Nat.add(k, 0n), fin, Equal.sym(Nat, Nat.add(k, 0n), k, Lemma.add_zero_right(k)), finEq), pEq, ctxF, rEq)' % TGT,
    'none => Empty.absurd(%s, G.ebnf_not_in_empty(%s, none))' % (GOAL, TARGET), '      '))
out.append('''    case 1n+d:
      Empty.absurd(%s, G.ebnf_not_in_empty(%s, hit))
''' % (GOAL, TARGET))

# ---- leaf ----
F = 'Spec.Leaf{tok} <> ts'
out.append('''# ---- A token ----

law leaf_follow:
''' + FIXD + POSD + '''  for +tok: Nat
  for +ts: +List<Spec.Tree>
  for +term: Nat
  for +rest: +List<Spec.Item>
''' + SEQD.replace('FOREST', F) + '''  for +sp: G.Spells(%s, input, k)
  for +restEq: {G.dropItems(1n+dot, %s) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(%s, grammar, Spec.Sym{Spec.Terminal{term}} <> rest) == True{} : Bool}
''' % (F, SEQ, F) + hitd(F) + ih('ihTs').replace('FOREST', 'ts') + '  ' + GOAL + '''

def leaf_follow(%s, %s, tok, ts, term, rest, %s, sp, restEq, fit, hit, ihTs):
  +fitTs = Lemma.and_true_right_side(Nat.is_eq(tok, term), Spec.fits(ts, grammar, rest), fit)
  +lts = Spec.leaves(ts)
  +finTs = Equal.trans(Nat, Nat.add(1n+k, List.length(&2, Nat, lts)), Nat.add(k, 1n+List.length(&2, Nat, lts)), fin, Equal.sym(Nat, Nat.add(k, 1n+List.length(&2, Nat, lts)), 1n+Nat.add(k, List.length(&2, Nat, lts)), Lemma.add_succ_right(k, List.length(&2, Nat, lts))), finEq)
''' % (FIX, POS, SEQA))
out.append(head_cases('Spec.at(index, prefix, 1n+dot, i, k, 1n+k)', 'Spec.walk(ts, False{}, index, prefix, 1n+dot, i, 1n+k)',
    end_hit('1n+k', 'ts', 'finTs'),
    call_ih('ihTs', 'False{}', 'rest', 'index', 'rpath', 'prefix', 'seqPrefix', '1n+dot', 'i', '1n+k', 'ff', 'fin', 'Spec.Group{}', '[]', 'pEq',
            'G.leaf_rest(input, k, tok, lts, sp)', seqready('restEq', 'fitTs', 'finTs', 'ctxF', 'foF', 'even', 'seqEq'), 'there')) + '\n')
open('walk.bend', 'w').write('\n'.join(out))

out = []
def case_law(name, comment, treeD, extraD, forest, ihs, body, params):
    s = '# ---- %s ----\n\nlaw %s:\n' % (comment, name) + FIXD + POSD + treeD + SEQD.replace('FOREST', forest)
    s += '  for +sp: G.Spells(%s, input, k)\n' % forest
    s += extraD + hitd(forest)
    for n, f in ihs:
        s += ih(n).replace('FOREST', f)
    s += '  ' + GOAL + '\n\ndef %s(%s, %s, %s, %s, sp, %s, hit, %s):\n' % (name, FIX, POS, params[0], SEQA, params[1], ', '.join(n for n, f in ihs))
    return s + body + '\n'

COMMONSPLIT = '''  +lch = Spec.leaves(CH)
  +lts = Spec.leaves(ts)
  +e1 = Nat.add(k, List.length(&2, Nat, lch))
  +finTs = Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lts)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, lts))), fin, G.end_split(k, lch, lts), finEq)
  +spTs = G.spells_second(input, k, lch, lts, sp)
  +spCh = G.spells_first(input, k, lch, lts, sp)
  +fitDrop = ''' + fitdrop('ts') + '\n'
def tail_ih(e, sp):
    return call_ih('ihTs', 'False{}', 'rest', 'index', 'rpath', 'prefix', 'seqPrefix', '1n+dot', 'i', e, 'ff', 'fin', 'Spec.Group{}', '[]', 'pEq', sp,
                   seqready('restEq', 'fitTs', 'finTs', 'ctxF', 'foF', 'even', 'seqEq'), 'inB')

# ---- node ----
F = 'Spec.Node{q, ch} <> ts'
walkCh = 'Spec.walk(ch, False{}, q, [], 0n, k, k)'
walkTs = 'Spec.walk(ts, False{}, index, prefix, 1n+dot, i, e1)'
body = '''  +h = Bool.and(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)))
  +hOk = Lemma.and_true_left(h, Spec.fits(ts, grammar, rest), fit)
  +lhsOk = Lemma.and_true_left(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
  +fitCh = Lemma.and_true_right_side(Spec.lhsIs(grammar, q, x), Spec.fits(ch, grammar, Spec.rhsOf(grammar, q)), hOk)
  +fitTs = Lemma.and_true_right_side(h, Spec.fits(ts, grammar, rest), fit)
''' + COMMONSPLIT.replace('CH', 'ch') + '''  +ctxCh = Pr.ctx_node(Gll.Predict{t}, grammar, start, input, index, rpath, dot, ff, x, q, ts, e1, fin, po, foF, itemEq, lhsOk, fitDrop, spTs, finTs, ctxF)
  +foCh = Pr.fo_node(Gll.Predict{t}, grammar, start, q, x, po, lhsOk)
''' + head_cases('Spec.at(index, prefix, 1n+dot, i, k, e1)', 'List.append(&2, Spec.Bsr, %s, %s)' % (walkCh, walkTs),
    end_hit('e1', 'ts', 'finTs'),
    '\n' + split_cases(walkCh, walkTs,
        call_ih('ihCh', 'False{}', 'Spec.rhsOf(grammar, q)', 'q', '[]', '[]', '[]', '0n', 'k', 'k', 'Gll.nestFuel()', 'e1', 'Spec.Group{}', '[]', '{==}', 'spCh',
                seqready('{==}', 'fitCh', '{==}', 'ctxCh', 'foCh', '{==}', '{==}'), 'inA'),
        tail_ih('e1', 'spTs')))
out.append(case_law('node_follow', 'A nonterminal', '''  for +q: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +x: Nat
  for +rest: +List<Spec.Item>
''', '''  for +itemEq: {Gll.nthItem(%s, dot) == Some{Spec.Sym{Spec.Nonterminal{x}}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, %s) == rest : +List<Spec.Item>}
  for +fit: {Spec.fits(%s, grammar, Spec.Sym{Spec.Nonterminal{x}} <> rest) == True{} : Bool}
''' % (SEQ, SEQ, F), F, [('ihCh', 'ch'), ('ihTs', 'ts')], body, ('q, ch, ts, x, rest', 'itemEq, restEq, fit')))

# ---- pick ----
F = 'Spec.Pick{a, ch} <> ts'
pre2 = 'List.append(&2, Nat, prefix, [dot, a])'
walkCh = 'Spec.walk(ch, False{}, index, %s, 0n, k, k)' % pre2
body = COMMONSPLIT.replace('CH', 'ch') + '''  +ctxCh = Pr.ctx_pick(Gll.Predict{t}, grammar, start, input, index, rpath, dot, a, ts, e1, fin, po, fitDrop, spTs, finTs, ctxF)
  +foCh = Pr.fo_pick(Gll.Predict{t}, ff, grammar, index, rpath, dot, bkind, balts, a, foF, itemEq, isA)
  +altEq = G.alt_seq(grammar, index, rpath, dot, a, bkind, balts, itemEq)
  +evenCh = Equal.trans(Bool, evenLength(%s), evenLength(prefix), True{}, even_snoc(prefix, dot, a), even)
  +seqCh = deeper_eq(grammar, index, prefix, rpath, dot, a, even, seqEq)
''' % pre2 + head_cases('Spec.at(index, prefix, 1n+dot, i, k, e1)', 'List.append(&2, Spec.Bsr, %s, %s)' % (walkCh, walkTs),
    end_hit('e1', 'ts', 'finTs'),
    '\n' + split_cases(walkCh, walkTs,
        call_ih('ihCh', 'False{}', 'Spec.altOf(balts, a)', 'index', 'a <> (dot <> rpath)', pre2, '[]', '0n', 'k', 'k', 'Adm.pred2(ff)', 'e1', 'Spec.Group{}', '[]',
                'G.prefix_ext(rpath, prefix, [dot, a], pEq)', 'spCh', seqready('altEq', 'fitCh', '{==}', 'ctxCh', 'foCh', 'evenCh', 'seqCh'), 'inA'),
        tail_ih('e1', 'spTs')))
out.append(case_law('pick_follow', 'A ( ) or [ ] that matched', '''  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
''', '''  for +itemEq: {Gll.nthItem(%s, dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, %s) == rest : +List<Spec.Item>}
  for +isA: {Spec.isAlt(balts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(balts, a)) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
''' % (SEQ, SEQ), F, [('ihCh', 'ch'), ('ihTs', 'ts')], body, ('a, ch, ts, bkind, balts, rest', 'itemEq, restEq, isA, fitCh, fitTs')))

# ---- skip ----
F = 'Spec.Skip{} <> ts'
walkTsK = 'Spec.walk(ts, False{}, index, prefix, 1n+dot, i, k)'
body = '''  +finTs = finEq
''' + head_cases('Spec.at(index, prefix, 1n+dot, i, k, k)', walkTsK, end_hit('k', 'ts', 'finTs'),
    tail_ih('k', 'sp').replace('inB)', 'there)'))
out.append(case_law('skip_follow', 'A skipped [ ] or an empty item', '''  for +ts: +List<Spec.Tree>
  for +rest: +List<Spec.Item>
''', '''  for +restEq: {G.dropItems(1n+dot, %s) == rest : +List<Spec.Item>}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
''' % SEQ, F, [('ihTs', 'ts')], body, ('ts, rest', 'restEq, fitTs')))

# ---- loop ----
F = 'Spec.Loop{rs} <> ts'
pre1 = 'List.append(&2, Nat, prefix, [dot])'
walkRs = 'Spec.walk(rs, True{}, index, %s, 0n, k, k)' % pre1
body = COMMONSPLIT.replace('CH', 'rs') + '''  +afterRs = Pr.after_loop(Gll.Predict{t}, grammar, start, input, index, rpath, dot, ts, e1, fin, po, fitDrop, spTs, finTs, ctxF)
''' + head_cases('Spec.at(index, prefix, 1n+dot, i, k, e1)', 'List.append(&2, Spec.Bsr, %s, %s)' % (walkRs, walkTs),
    end_hit('e1', 'ts', 'finTs'),
    '\n' + split_cases(walkRs, walkTs,
        call_ih('ihRs', 'True{}', '[]', 'index', 'dot <> rpath', pre1, 'prefix', '0n', 'k', 'k', 'ff', 'e1', 'bkind', 'balts',
                'G.prefix_ext(rpath, prefix, [dot], pEq)', 'spCh', '(itemEq, (loopOk, (fitRs, ({==}, (afterRs, (foF, ({==}, (even, seqEq))))))))', 'inA'),
        tail_ih('e1', 'spTs')))
out.append(case_law('loop_follow', 'A loop', '''  for +rs: +List<Spec.Tree>
  for +ts: +List<Spec.Tree>
  for +bkind: Spec.Bracket
  for +balts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
''', '''  for +itemEq: {Gll.nthItem(%s, dot) == Some{Spec.Brack{bkind, balts}} : Maybe<&2, Spec.Item>}
  for +restEq: {G.dropItems(1n+dot, %s) == rest : +List<Spec.Item>}
  for +loopOk: {Gll.isLoop(bkind) == True{} : Bool}
  for +fitRs: {Spec.fits(rs, grammar, Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})) == True{} : Bool}
  for +fitTs: {Spec.fits(ts, grammar, rest) == True{} : Bool}
''' % (SEQ, SEQ), F, [('ihRs', 'rs'), ('ihTs', 'ts')], body, ('rs, ts, bkind, balts, rest', 'itemEq, restEq, loopOk, fitRs, fitTs')))

open('walk2.bend', 'w').write('\n'.join(out))

out = []
# ---- rounds ----
F = 'Spec.Pick{a, ch} <> rest'
preA = 'List.append(&2, Nat, prefix, [a])'
walkCh = 'Spec.walk(ch, False{}, index, %s, 0n, i, k)' % preA
walkRest = 'Spec.walk(rest, True{}, index, prefix, 0n, i, e1)'
ROUNDD = '''  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(%s, input, k)
  for +finEq: {Nat.add(k, List.length(&2, Nat, Spec.leaves(%s))) == fin : Nat}
  for +after: {Pr.afterOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +foL: {Pr.foLoop(Gll.Predict{t}, ff, grammar, index, rpath) == True{} : Bool}
  for +preEq: {prefix == List.append(&2, Nat, seqPrefix, [headOf(rpath)]) : +List<Nat>}
  for +evenS: {evenLength(seqPrefix) == True{} : Bool}
  for +seqEqS: {Spec.sequenceAt(grammar, index, seqPrefix) == Gll.seqAt(grammar, index, tailOf(rpath)) : +List<Nat>}
  for +itemEq: {G.loopItem(grammar, index, rpath) == Some{Spec.Brack{kind, alts}} : Maybe<&2, Spec.Item>}
  for +loopOk: {Gll.isLoop(kind) == True{} : Bool}
  for +isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for +fitCh: {Spec.fits(ch, grammar, Spec.altOf(alts, a)) == True{} : Bool}
  for +fitRest: {Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}
''' % (F, F)
ROUNDD = ROUNDD.replace('Gll.seqAt(grammar, index, tailOf(rpath)) : +List<Nat>}', 'Gll.seqAt(grammar, index, tailOf(rpath)) : +List<Spec.Item>}')
s = '''# ---- A round of a loop ----

law round_follow:
  for rpath: +List<Nat>
''' + FIXD + '''  for +index: Nat
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
''' + ROUNDD + hitd(F, 'True{}') + ih('ihCh').replace('FOREST', 'ch') + ih('ihRest').replace('FOREST', 'rest') + '  ' + GOAL + '''

def round_follow(rpath, %s, index, prefix, seqPrefix, dot, i, k, ff, fin, a, ch, rest, kind, alts, pEq, sp, finEq, after, foL, preEq, evenS, seqEqS, itemEq, loopOk, isA, fitCh, fitRest, hit, ihCh, ihRest):
  match rpath:
    case Nil{}:
      Empty.absurd(%s, Lemma.true_is_not_false(Equal.cong(Maybe<&2, Spec.Item>, Bool, v => G.isNone(v), None{}, Some{Spec.Brack{kind, alts}}, itemEq)))
    case Con{+m, +outer}:
      +remCh = Equal.cong(Maybe<&2, Spec.Item>, +List<Spec.Item>, v => Gll.bracketAlt(v, a), Gll.nthItem(Gll.seqAt(grammar, index, outer), m), Some{Spec.Brack{kind, alts}}, itemEq)
      +lch = Spec.leaves(ch)
      +lrest = Spec.leaves(rest)
      +e1 = Nat.add(k, List.length(&2, Nat, lch))
      +spCh = G.spells_first(input, k, lch, lrest, sp)
      +spRest = G.spells_second(input, k, lch, lrest, sp)
      +finRest = Equal.trans(Nat, Nat.add(e1, List.length(&2, Nat, lrest)), Nat.add(k, List.length(&2, Nat, List.append(&2, Nat, lch, lrest))), fin, G.end_split(k, lch, lrest), finEq)
      +ctxCh = Pr.ctx_round(Gll.Predict{t}, grammar, start, input, index, m <> outer, a, kind, alts, rest, e1, fin, po, itemEq, loopOk, after, fitRest, spRest, finRest)
      +foCh = Pr.fo_round(Gll.Predict{t}, ff, grammar, index, m <> outer, kind, alts, a, foL, itemEq, isA)
      +longer = List.append(&2, Nat, seqPrefix, [m, a])
      +eqP = Equal.trans(+List<Nat>, %s, List.append(&2, Nat, List.append(&2, Nat, seqPrefix, [m]), [a]), longer,
        Equal.cong(+List<Nat>, +List<Nat>, v => List.append(&2, Nat, v, [a]), prefix, List.append(&2, Nat, seqPrefix, [m]), preEq),
        G.nat_append_assoc(seqPrefix, [m], [a]))
      +evenCh = Equal.trans(Bool, evenLength(%s), evenLength(longer), True{}, Equal.cong(+List<Nat>, Bool, v => evenLength(v), %s, longer, eqP),
        Equal.trans(Bool, evenLength(longer), evenLength(seqPrefix), True{}, even_snoc(seqPrefix, m, a), evenS))
      +seqCh = Equal.trans(+List<Spec.Item>, Spec.sequenceAt(grammar, index, %s), Spec.sequenceAt(grammar, index, longer), Gll.seqAt(grammar, index, a <> (m <> outer)),
        Equal.cong(+List<Nat>, +List<Spec.Item>, v => Spec.sequenceAt(grammar, index, v), %s, longer, eqP),
        deeper_eq(grammar, index, seqPrefix, outer, m, a, evenS, seqEqS))
''' % (FIX, GOAL, preA, preA, preA, preA, preA)
s += split_cases(walkCh, walkRest,
    call_ih('ihCh', 'False{}', 'Spec.altOf(alts, a)', 'index', 'a <> (m <> outer)', preA, '[]', '0n', 'i', 'k', 'Adm.pred2(ff)', 'e1', 'Spec.Group{}', '[]',
            'G.prefix_ext(m <> outer, prefix, [a], pEq)', 'spCh', seqready('remCh', 'fitCh', '{==}', 'ctxCh', 'foCh', 'evenCh', 'seqCh'), 'inA'),
    call_ih('ihRest', 'True{}', '[]', 'index', 'm <> outer', 'prefix', 'seqPrefix', '0n', 'i', 'e1', 'ff', 'fin', 'kind', 'alts', 'pEq', 'spRest',
            '(itemEq, (loopOk, (fitRest, (finRest, (after, (foL, (preEq, (evenS, seqEqS))))))))', 'inB'), '      ').replace('member_split(%s, %s, %s, there)' % (walkCh, walkRest, TARGET), 'member_split(%s, %s, %s, hit)' % (walkCh, walkRest, TARGET)) + '\n'
out.append(s)
open('walk3.bend', 'w').write('\n'.join(out))

out = []
ITEMS = [('Nil', 'Nil{}', None), ('T', 'Con{Spec.Sym{Spec.Terminal{+term}}, +rest}', 'Spec.Sym{Spec.Terminal{term}}'),
         ('N', 'Con{Spec.Sym{Spec.Nonterminal{+x}}, +rest}', 'Spec.Sym{Spec.Nonterminal{x}}'),
         ('G', 'Con{Spec.Brack{Spec.Group{}, +balts}, +rest}', 'Spec.Brack{Spec.Group{}, balts}'),
         ('O', 'Con{Spec.Brack{Spec.Optional{}, +balts}, +rest}', 'Spec.Brack{Spec.Optional{}, balts}'),
         ('C', 'Con{Spec.Brack{Spec.Closure{}, +balts}, +rest}', 'Spec.Brack{Spec.Closure{}, balts}'),
         ('P', 'Con{Spec.Brack{Spec.Positive{}, +balts}, +rest}', 'Spec.Brack{Spec.Positive{}, balts}'),
         ('E', 'Con{Spec.Eps{}, +rest}', 'Spec.Eps{}')]
KIND = {'C': 'Spec.Closure{}', 'P': 'Spec.Positive{}', 'G': 'Spec.Group{}', 'O': 'Spec.Optional{}'}
READY = '(rem0, (fit0, (finEq, (ctxF, (foF, (even, seqEq))))))'
def prelude(it, forest):
    return '''          +rem = {rem0 : {G.dropItems(dot, %s) == %s <> rest : +List<Spec.Item>}}
          +fit = {fit0 : {Spec.fits(%s, grammar, %s <> rest) == True{} : Bool}}
          +itemEq = G.drop_next(dot, %s, %s, rest, rem)
          +restEq = G.drop_succ(dot, %s, %s, rest, rem)
''' % (SEQ, it, forest, it, SEQ, it, SEQ, it)
def disp(name, treeD, treeA, forest, ihs, real):
    s = 'law %s:\n  for items: +List<Spec.Item>\n' % name + FIXD + POSD + '  for +kind: Spec.Bracket\n  for +alts: +List<+List<Spec.Item>>\n' + treeD
    s += '  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}\n  for +sp: G.Spells(%s, input, k)\n' % forest
    s += '  for ready: Ready(False{}, grammar, t, input, %s, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)\n' % forest
    s += hitd(forest)
    for n, f in ihs:
        s += ih(n).replace('FOREST', f)
    s += '  %s\n\ndef %s(items, %s, %s, kind, alts, %s, pEq, sp, ready, hit, %s):\n  match items:\n' % (GOAL, name, FIX, POS, treeA, ', '.join(n for n, f in ihs))
    for key, pat, it in ITEMS:
        s += '    case %s:\n      match ready:\n        case %s:\n' % (pat, READY)
        if key in real:
            s += prelude(it, forest) + real[key]
        else:
            s += '          Empty.absurd(%s, Lemma.false_is_not_true(fit0))\n' % GOAL
    return s
CALL = lambda name, args: '          %s(%s, %s, %s)\n' % (name, FIX, POS, args)
out.append(disp('leaf_disp', '  for +tok: Nat\n  for +ts: +List<Spec.Tree>\n', 'tok, ts', 'Spec.Leaf{tok} <> ts', [('ihTs', 'ts')],
    {'T': CALL('leaf_follow', 'tok, ts, term, rest, %s, sp, restEq, fit, hit, ihTs' % SEQA)}))
out.append(disp('node_disp', '  for +q: Nat\n  for +ch: +List<Spec.Tree>\n  for +ts: +List<Spec.Tree>\n', 'q, ch, ts', 'Spec.Node{q, ch} <> ts', [('ihCh', 'ch'), ('ihTs', 'ts')],
    {'N': CALL('node_follow', 'q, ch, ts, x, rest, %s, sp, itemEq, restEq, fit, hit, ihCh, ihTs' % SEQA)}))
pickG = '''          +hP = Bool.and(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, rest), fit)
''' + CALL('pick_follow', 'a, ch, ts, Spec.Group{}, balts, rest, %s, sp, itemEq, restEq, Lemma.and_true_left(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk), Lemma.and_true_right_side(Spec.isAlt(balts, a), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk), Lemma.and_true_right_side(hP, Spec.fits(ts, grammar, rest), fit), hit, ihCh, ihTs' % SEQA)
pickO = '''          +okR = Spec.roundsOk(Spec.Optional{}, [Spec.Pick{a, ch}])
          +hP = Bool.and(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)))
          +hOk = Lemma.and_true_left(hP, Spec.fits(ts, grammar, rest), fit)
          +altOk = Lemma.and_true_left(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk)
''' + CALL('pick_follow', 'a, ch, ts, Spec.Optional{}, balts, rest, %s, sp, itemEq, restEq, Lemma.and_true_right_side(okR, Spec.isAlt(balts, a), altOk), Lemma.and_true_right_side(Bool.and(okR, Spec.isAlt(balts, a)), Spec.fits(ch, grammar, Spec.altOf(balts, a)), hOk), Lemma.and_true_right_side(hP, Spec.fits(ts, grammar, rest), fit), hit, ihCh, ihTs' % SEQA)
out.append(disp('pick_disp', '  for +a: Nat\n  for +ch: +List<Spec.Tree>\n  for +ts: +List<Spec.Tree>\n', 'a, ch, ts', 'Spec.Pick{a, ch} <> ts', [('ihCh', 'ch'), ('ihTs', 'ts')],
    {'G': pickG, 'O': pickO}))
skipC = CALL('skip_follow', 'ts, rest, %s, sp, restEq, fit, hit, ihTs' % SEQA)
out.append(disp('skip_disp', '  for +ts: +List<Spec.Tree>\n', 'ts', 'Spec.Skip{} <> ts', [('ihTs', 'ts')], {'O': skipC, 'E': skipC}))
def loopC(K):
    k = KIND[K]
    tms = 'Spec.times(List.length(&2, Spec.Tree, rs), Spec.Brack{Spec.Group{}, balts})'
    return '''          +okR = Spec.roundsOk(%s, rs)
          +both = Lemma.and_true_left(Bool.and(okR, Spec.fits(rs, grammar, %s)), Spec.fits(ts, grammar, rest), fit)
''' % (k, tms) + CALL('loop_follow', 'rs, ts, %s, balts, rest, %s, sp, itemEq, restEq, {==}, Lemma.and_true_right_side(okR, Spec.fits(rs, grammar, %s), both), Lemma.and_true_right_side(Bool.and(okR, Spec.fits(rs, grammar, %s)), Spec.fits(ts, grammar, rest), fit), hit, ihRs, ihTs' % (k, SEQA, tms, tms))
out.append(disp('loop_disp', '  for +rs: +List<Spec.Tree>\n  for +ts: +List<Spec.Tree>\n', 'rs, ts', 'Spec.Loop{rs} <> ts', [('ihRs', 'rs'), ('ihTs', 'ts')], {'C': loopC('C'), 'P': loopC('P')}))

# ---- rounds dispatch ----
out.append('''law round_disp:
  for rpath: +List<Nat>
''' + FIXD + '''  for +index: Nat
  for +prefix: +List<Nat>
  for +seqPrefix: +List<Nat>
  for +dot: Nat
  for +i: Nat
  for +k: Nat
  for +ff: Nat
  for +fin: Nat
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +ch: +List<Spec.Tree>
  for +rest: +List<Spec.Tree>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(Spec.Pick{a, ch} <> rest, input, k)
  for ready: Ready(True{}, grammar, t, input, Spec.Pick{a, ch} <> rest, index, rpath, prefix, seqPrefix, dot, k, ff, fin, [], kind, alts)
''' + hitd('Spec.Pick{a, ch} <> rest', 'True{}') + ih('ihCh').replace('FOREST', 'ch') + ih('ihRest').replace('FOREST', 'rest') + '  ' + GOAL + '''

def round_disp(rpath, %s, index, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, a, ch, rest, pEq, sp, ready, hit, ihCh, ihRest):
  match ready:
    case (itemEq, (loopOk, (fit0, (finEq, (after, (foL, (preEq, (evenS, seqEqS)))))))):
      +fit = {fit0 : {Spec.fits(Spec.Pick{a, ch} <> rest, grammar, Spec.times(List.length(&2, Spec.Tree, Spec.Pick{a, ch} <> rest), Spec.Brack{Spec.Group{}, alts})) == True{} : Bool}}
      +h = Bool.and(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)))
      +R = Spec.fits(rest, grammar, Spec.times(List.length(&2, Spec.Tree, rest), Spec.Brack{Spec.Group{}, alts}))
      +hOk = Lemma.and_true_left(h, R, fit)
      round_follow(rpath, %s, index, prefix, seqPrefix, dot, i, k, ff, fin, a, ch, rest, kind, alts, pEq, sp, finEq, after, foL, preEq, evenS, seqEqS, itemEq, loopOk,
        Lemma.and_true_left(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
        Lemma.and_true_right_side(Spec.isAlt(alts, a), Spec.fits(ch, grammar, Spec.altOf(alts, a)), hOk),
        Lemma.and_true_right_side(h, R, fit), hit, ihCh, ihRest)
''' % (FIX, FIX))

# ---- the walk ----
WP = 'index, rpath, prefix, seqPrefix, dot, i, k, ff, fin, items, kind, alts'
def lam(f):
    return '(ri => ix => rx => px => sx => dx => cx => qx => fx => nx => its => kx => ax => pe => spx => rd => hx => follow_walk(%s, ri, %s, ix, rx, px, sx, dx, cx, qx, fx, nx, its, kx, ax, pe, spx, rd, hx))' % (f, FIX)
s = '''# Wherever the walk of a parse tree lists the end step of a sequence, the token where it
# ends is in the tables' context for that sequence.
law follow_walk:
  for forest: +List<Spec.Tree>
  for rounds: Bool
''' + FIXD + POSD + '''  for +items: +List<Spec.Item>
  for +kind: Spec.Bracket
  for +alts: +List<+List<Spec.Item>>
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +sp: G.Spells(forest, input, k)
  for ready: Ready(rounds, grammar, t, input, forest, index, rpath, prefix, seqPrefix, dot, k, ff, fin, items, kind, alts)
''' + hitd('forest', 'rounds') + '  ' + GOAL + '''

def follow_walk(forest, rounds, %s, %s, pEq, sp, ready, hit):
  match forest rounds:
    case Nil{} False{}:
      match ready:
        case %s:
          empty_follow(dot, %s, index, rpath, prefix, i, k, fin, pEq, finEq, ctxF, hit)
    case Nil{} True{}:
      Empty.absurd(%s, G.ebnf_not_in_empty(%s, hit))
''' % (FIX, WP, READY, FIX, GOAL, TARGET)
A = '%s, %s, kind, alts' % (FIX, POS)
s += '    case Con{Spec.Leaf{+tok}, +ts} False{}:\n      leaf_disp(items, %s, tok, ts, pEq, sp, ready, hit, %s)\n' % (A, lam('ts'))
s += '    case Con{Spec.Node{+q, +ch}, +ts} False{}:\n      node_disp(items, %s, q, ch, ts, pEq, sp, ready, hit, %s, %s)\n' % (A, lam('ch'), lam('ts'))
s += '    case Con{Spec.Pick{+a, +ch}, +ts} False{}:\n      pick_disp(items, %s, a, ch, ts, pEq, sp, ready, hit, %s, %s)\n' % (A, lam('ch'), lam('ts'))
s += '    case Con{Spec.Skip{}, +ts} False{}:\n      skip_disp(items, %s, ts, pEq, sp, ready, hit, %s)\n' % (A, lam('ts'))
s += '    case Con{Spec.Loop{+rs}, +ts} False{}:\n      loop_disp(items, %s, rs, ts, pEq, sp, ready, hit, %s, %s)\n' % (A, lam('rs'), lam('ts'))
s += '    case Con{Spec.Pick{+a, +ch}, +rest} True{}:\n      round_disp(rpath, %s, index, prefix, seqPrefix, dot, i, k, ff, fin, kind, alts, a, ch, rest, pEq, sp, ready, hit, %s, %s)\n' % (FIX, lam('ch'), lam('rest'))
for pat in ['Spec.Leaf{tok}', 'Spec.Node{q, ch}', 'Spec.Skip{}', 'Spec.Loop{rs}']:
    s += '    case Con{%s, rest} True{}:\n      Empty.absurd(%s, G.ebnf_not_in_empty(%s, hit))\n' % (pat, GOAL, TARGET)
out.append(s)
open('walk4.bend', 'w').write('\n'.join(out))
