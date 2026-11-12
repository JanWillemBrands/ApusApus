
# ======== THE STEPS OF A STATE ON THE TREE ========

law on_right:
  for xs: +List<Support.Fact>
  for +ys: +List<Support.Fact>
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +h: AllOn(grammar, input, root, List.append(&2, Support.Fact, xs, ys))
  AllOn(grammar, input, root, ys)

def on_right(xs, ys, grammar, input, root, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      match h:
        case (h0, t0):
          +tl = {t0 : AllOn(grammar, input, root, List.append(&2, Support.Fact, rest, ys))}
          on_right(rest, ys, grammar, input, root, tl)

law steps_on:
  for ys: +List<Spec.Bsr>
  for +y: Spec.Bsr
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +h: AllOn(grammar, input, root, Support.stepFacts(ys))
  for +m: {Spec.bsrMember(y, ys) == True{} : Bool}
  {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}

def steps_on(ys, y, grammar, input, root, h, m):
  match ys:
    case Nil{}:
      Empty.absurd({Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}, G.ebnf_not_in_empty(y, m))
    case Con{+z, +rest}:
      match h:
        case (h0, t0):
          +hz = {h0 : {Spec.bsrMember(z, Spec.steps(root, 0n)) == True{} : Bool}}
          +tl = {t0 : AllOn(grammar, input, root, Support.stepFacts(rest))}
          L.either_case({y == z : Spec.Bsr}, {Spec.bsrMember(y, rest) == True{} : Bool}, {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}, G.ebnf_member_cases(y, z, rest, m),
            same => Equal.trans(Bool, Spec.bsrMember(y, Spec.steps(root, 0n)), Spec.bsrMember(z, Spec.steps(root, 0n)), True{}, Equal.cong(Spec.Bsr, Bool, v => Spec.bsrMember(v, Spec.steps(root, 0n)), y, z, same), hz),
            later => steps_on(rest, y, grammar, input, root, tl, later))

law state_steps_on:
  for s: Gll.GState
  for +y: Spec.Bsr
  for +grammar: +List<Spec.Production>
  for +input: +List<Nat>
  for +root: Spec.Tree
  for +h: AllOn(grammar, input, root, Support.factsOf(s))
  for +m: {Spec.bsrMember(y, Check.stepsOf(s)) == True{} : Bool}
  {Spec.bsrMember(y, Spec.steps(root, 0n)) == True{} : Bool}

def state_steps_on(s, y, grammar, input, root, h, m):
  match s:
    case Gll.GState{+seen, todo, +cs, +rs, +ps, +ys}:
      +f1 = Support.descriptorFacts(seen)
      +f2 = Support.clusterFacts(cs)
      +f3 = Support.returnFacts(rs)
      +f4 = Support.popFacts(ps)
      +f5 = Support.stepFacts(ys)
      +h2 = on_right(f1, List.append(&2, Support.Fact, f2, List.append(&2, Support.Fact, f3, List.append(&2, Support.Fact, f4, f5))), grammar, input, root, h)
      +h3 = on_right(f2, List.append(&2, Support.Fact, f3, List.append(&2, Support.Fact, f4, f5)), grammar, input, root, h2)
      +h4 = on_right(f3, List.append(&2, Support.Fact, f4, f5), grammar, input, root, h3)
      +h5 = on_right(f4, f5, grammar, input, root, h4)
      steps_on(ys, y, grammar, input, root, h5, m)

# ======== THE LAW ========

law state_exact:
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +input: +List<Nat>
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for +s: Gll.GState
  for +set: +List<Spec.Bsr>
  for facts: {Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s)) == True{} : Bool} & {Check.stepsOf(s) == set : +List<Spec.Bsr>}
  Spec.IsExactBsr(grammar, start, input, set)

def state_exact(grammar, start, t, ll1, plain, input, tree, fit, sp, s, set, facts):
  match facts:
    case (ok0, same0):
      +ok = {ok0 : {Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s)) == True{} : Bool}}
      +same = {same0 : {Check.stepsOf(s) == set : +List<Spec.Bsr>}}
      +closedRoot = Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s))
      +cr = Lemma.and_true_left(closedRoot, PS.supportedWith(Gll.Predict{t}, grammar, start, input, s), ok)
      +sup = Lemma.and_true_right_side(closedRoot, PS.supportedWith(Gll.Predict{t}, grammar, start, input, s), ok)
      +po = Lemma.and_true_left(First.tablesClosed(grammar, start, t), List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), ll1)
      +noConf = Lemma.and_true_right_side(First.tablesClosed(grammar, start, t), List.is_empty(&2, LL1.Conflict, LL1.conflictsOf(grammar, t)), ll1)
      +onTree = supported_on(grammar, start, t, po, noConf, input, tree, fit, sp, plain, s, sup)
      (+element => +m =>
        (tree, (fit, (sp, state_steps_on(s, element, grammar, input, tree, onTree,
          Equal.trans(Bool, Spec.bsrMember(element, Check.stepsOf(s)), Spec.bsrMember(element, set), True{}, Equal.cong(+List<Spec.Bsr>, Bool, v => Spec.bsrMember(element, v), Check.stepsOf(s), set, same), m))))),
       G.state_done(Gll.Predict{t}, grammar, start, input, s, set, po, (cr, same)))

law run_exact:
  for r: Gll.GRun
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +t: Gll.Tables
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +input: +List<Nat>
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for +set: +List<Spec.Bsr>
  for got: {PS.runLL(r, Gll.Predict{t}, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

def run_exact(r, grammar, start, t, ll1, plain, input, tree, fit, sp, set, got):
  match r:
    case Gll.GDone{+s}:
      +ok = Bool.and(Bool.and(Check.closedWith(Gll.Predict{t}, grammar, input, s), Check.clusterIn(Gll.CKey{Gll.TNt{start}, 0n}, s)), PS.supportedWith(Gll.Predict{t}, grammar, start, input, s))
      state_exact(grammar, start, t, ll1, plain, input, tree, fit, sp, s, set, G.check_pick(ok, s, set, got))
    case Gll.OutOfFuel{s}:
      Empty.absurd(Spec.IsExactBsr(grammar, start, input, set), Lemma.true_is_not_false(Equal.cong(Maybe<&2, +List<Spec.Bsr>>, Bool, v => G.isNothing(v), None{}, Some{set}, got)))

# NO DEAD WOOD, FOR A GRAMMAR WITHOUT BRACKETS.
law ll1_no_dead_wood_bnf:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for +plain: {PS.withoutBrackets(grammar) == True{} : Bool}
  for +t: Gll.Tables
  for +tablesEq: {First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start) == Some{t} : Maybe<&2, Gll.Tables>}
  for +ll1: {LL1.ll1ByTables(grammar, start, t) == True{} : Bool}
  for +tree: Spec.Tree
  for +fit: {Spec.fits([tree], grammar, [Spec.Sym{Spec.Nonterminal{start}}]) == True{} : Bool}
  for +sp: {Spec.leaves([tree]) == input : +List<Nat>}
  for got: {PS.llSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.IsExactBsr(grammar, start, input, set)

def ll1_no_dead_wood_bnf(fuel, grammar, start, input, set, plain, t, tablesEq, ll1, tree, fit, sp, got):
  +tb = First.tablesOf(Nat.add(Nat.mul(First.ntCount(grammar), 4n), 4n), grammar, start)
  run_exact(Gll.parseWith(fuel, Gll.Predict{t}, grammar, start, input), grammar, start, t, ll1, plain, input, tree, fit, sp, set,
    Equal.trans(Maybe<&2, +List<Spec.Bsr>>, PS.llPick(Some{t}, fuel, grammar, start, input), PS.llPick(tb, fuel, grammar, start, input), Some{set},
      Equal.cong(Maybe<&2, Gll.Tables>, Maybe<&2, +List<Spec.Bsr>>, v => PS.llPick(v, fuel, grammar, start, input), Some{t}, tb, Equal.sym(Maybe<&2, Gll.Tables>, tb, Some{t}, tablesEq)), got))
