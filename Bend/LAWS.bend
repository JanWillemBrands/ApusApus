import Base
import ./SPEC.bend as Spec
import ./GLL.bend as Gll
import ./CHECK.bend as Check

# THE LAWS: every claim, and nothing else. Each law is proven in PROOF_TREES.bend or
# PROOF_GLL.bend; `bend PROOF.bend` checks them all.
#
# What the laws talk about is defined in SPEC.bend. The parser in GLL.bend is not
# trusted: its output is only handed out by CHECK.bend after a check.

# REWRITING LAWS. Each bracket means its usual BNF rewriting, stated on sentential
# forms (items followed by `rest`), without ever making a helper nonterminal:
#   ( τ1 | .. | τn ) η   derives what some  τa η  derives
#   [ τ ] η              derives what  η  or  ( τ ) η  derives
#   { τ } η              derives what  η  or  ( τ ) { τ } η  derives
#   < τ > η              derives what  ( τ ) { τ } η  derives
# together with the BNF steps for symbols. Proofs of algorithms reason with these.

law empty_derives:
  for +grammar: +List<Spec.Production>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, [], w)
  {w == [] : +List<Nat>}

law terminal_unfold:
  for +grammar: +List<Spec.Production>
  for +k: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Sym{Spec.Terminal{k}} <> rest, w)
  exs w2: +List<Nat>
  {w == k <> w2 : +List<Nat>} & Spec.Derives(grammar, rest, w2)

law nonterminal_unfold:
  for +grammar: +List<Spec.Production>
  for +a: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Sym{Spec.Nonterminal{a}} <> rest, w)
  exs p: Nat
  {Spec.lhsIs(grammar, p, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)

law nonterminal_fold:
  for +grammar: +List<Spec.Production>
  for +a: Nat
  for +p: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for lhsOk: {Spec.lhsIs(grammar, p, a) == True{} : Bool}
  for d: Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.rhsOf(grammar, p), rest), w)
  Spec.Derives(grammar, Spec.Sym{Spec.Nonterminal{a}} <> rest, w)

law group_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)
  exs a: Nat
  {Spec.isAlt(alts, a) == True{} : Bool} & Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)

law group_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +a: Nat
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for isA: {Spec.isAlt(alts, a) == True{} : Bool}
  for d: Spec.Derives(grammar, List.append(&2, Spec.Item, Spec.altOf(alts, a), rest), w)
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)

law optional_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w)
  Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>

law optional_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> rest, w)>
  Spec.Derives(grammar, Spec.Brack{Spec.Optional{}, alts} <> rest, w)

law closure_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Closure{}, alts} <> rest, w)
  Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>

law closure_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Either<Spec.Derives(grammar, rest, w), Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)>
  Spec.Derives(grammar, Spec.Brack{Spec.Closure{}, alts} <> rest, w)

law positive_unfold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)

law positive_fold:
  for +grammar: +List<Spec.Production>
  for +alts: +List<+List<Spec.Item>>
  for +rest: +List<Spec.Item>
  for +w: +List<Nat>
  for d: Spec.Derives(grammar, Spec.Brack{Spec.Group{}, alts} <> Spec.Brack{Spec.Closure{}, alts} <> rest, w)
  Spec.Derives(grammar, Spec.Brack{Spec.Positive{}, alts} <> rest, w)

# THE CHECKED GLL PARSER MISSES NOTHING. Whenever the checked GLL parser hands out a set of steps, no
# step of any parse tree of the input is missing from it. The engine itself is not
# trusted: what it hands out passed the closedness check.
law gll_every_parse_step:
  for fuel: Nat
  for +grammar: +List<Spec.Production>
  for +start: Nat
  for +input: +List<Nat>
  for +set: +List<Spec.Bsr>
  for got: {Check.checkedSteps(fuel, grammar, start, input) == Some{set} : Maybe<&2, +List<Spec.Bsr>>}
  Spec.EveryParseStep(grammar, start, input, set)
