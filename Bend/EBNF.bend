import Base
import ./SYNTAX.bend as Spec
import ./CORE.bend as Core

# WHAT A GRAMMAR AS WRITTEN MEANS: its translation to the core.
#
# A grammar as written (SYNTAX.bend) has productions whose right sides are items: a symbol, a
# bracket ( ) [ ] { } < > around alternatives, or ε. What it means is the core grammar it
# translates to (CORE.bend): its parse trees are the core trees of that grammar. Each
# bracket becomes a group nonterminal G, whose productions are its alternatives as written,
# and [ ], { }, < > add a shape nonterminal H (and < > a tail K) with fixed productions:
#
#     ( τ1 | … | τn )   G = τ1 | … | τn
#     [ … ]             H = ε | G!
#     { … }             H = ε | H G!                   (towards Swift)
#                       H = ε | G! H                   (towards LL(1))
#     < … >             H = G⁰ | K,  K = G! | K G!     (towards Swift)
#                       H = G⁰ | G! K,  K = ε | G! K   (towards LL(1))
#     ε                 E = ε, one E for the grammar
#
# G! must read something, G⁰ nothing (Core.Need): the pick of a [ ] reads something, every
# round of a loop does, and a < > over nothing has its one empty round. A loop's body is a
# group, as Swift Apus builds it: { τ } and { ( τ ) } mean the same. Towards Swift, loops are
# left-recursive, so the steps are Swift's (each round chained from the loop's start);
# towards LL(1) they are right-recursive, so "another round or stop" is chosen where each
# round would start. Generated productions carry no annotation: they are never ranked,
# marked or guarded.

# ======== PASS 1: NAMES BY POSITION ========
#
# A new nonterminal is named by where its bracket stands, so the walk needs no counter:
# Group{index, path} is the group of the bracket whose alternatives are at path ++ [a];
# Shape and Tail are named by the bracket's own path.

type Name is Data:
  Written{id: Nat}
  Group{index: Nat, path: +List<Nat>}
  Shape{index: Nat, path: +List<Nat>}
  Tail{index: Nat, path: +List<Nat>}
  Epsilon{}

type NamedSym is Data:
  Token{kind: Nat}
  Ref{name: Name, need: Core.Need}

# Which of a production's steps Swift Apus records, and under which of its slots.
#   Sequence{index, path}  the sequence at (index, path) as written: dot d is slot path ++ [d]
#   Rounds{index, link, d} a loop's shape: its step at dot d is the round's link step
#   Hidden                 no step of Swift's (shapes, E)
type Origin is Data:
  Sequence{index: Nat, path: +List<Nat>}
  Rounds{index: Nat, link: +List<Nat>, dot: Nat}
  Hidden{}

type NamedProduction is Data:
  NamedProduction{lhs: Name, rhs: +List<NamedSym>, origin: Origin}

# What a walk gives: the symbols of a sequence, the productions below it, the new names it
# declares, one more than the largest written nonterminal it saw, and whether the nesting
# fuel lasted.
type Out is Data:
  Out{syms: +List<NamedSym>, prods: +List<NamedProduction>, names: +List<Name>, top: Nat, ok: Bool}

def emptyOut() -> Out:
  Out{[], [], [], 0n, True{}}

def consSym(+s: NamedSym, +top: Nat, o: Out) -> Out:
  match o:
    case Out{+syms, +prods, +names, +t, +ok}:
      Out{s <> syms, prods, names, Nat.max(top, t), ok}

# A loop's body: { ( τ ) } and { τ } both have τ's alternatives as the group's.
def bodyOf(alts: +List<+List<Spec.Item>>) -> +List<+List<Spec.Item>>:
  match alts:
    case Con{Con{Spec.Brack{Spec.Group{}, +inner}, Nil{}}, Nil{}}:
      inner
    case +other:
      other

# Where a bracket's alternatives stand: for ( ) and [ ] at here ++ [a]; a loop's are inside
# its implicit group, at here ++ [0, 0, a], and the round's link step is slot here ++ [0, 1].
def groupPath(kind: Spec.Bracket, +here: +List<Nat>) -> +List<Nat>:
  match kind:
    case Spec.Group{}:
      here
    case Spec.Optional{}:
      here
    case Spec.Closure{}:
      List.append(&2, Nat, here, [0n, 0n])
    case Spec.Positive{}:
      List.append(&2, Nat, here, [0n, 0n])

def bodyFor(kind: Spec.Bracket, +alts: +List<+List<Spec.Item>>) -> +List<+List<Spec.Item>>:
  match kind:
    case Spec.Group{}:
      alts
    case Spec.Optional{}:
      alts
    case Spec.Closure{}:
      bodyOf(alts)
    case Spec.Positive{}:
      bodyOf(alts)

def shapeProds(kind: Spec.Bracket, +left: Bool, +g: Name, +h: Name, +t: Name, +index: Nat, +link: +List<Nat>) -> +List<NamedProduction>:
  match kind left:
    case Spec.Group{} _:
      []
    case Spec.Optional{} _:
      [NamedProduction{h, [], Hidden{}}, NamedProduction{h, [Ref{g, Core.Something{}}], Hidden{}}]
    case Spec.Closure{} True{}:
      [NamedProduction{h, [], Hidden{}}, NamedProduction{h, [Ref{h, Core.Anything{}}, Ref{g, Core.Something{}}], Rounds{index, link, 2n}}]
    case Spec.Closure{} False{}:
      [NamedProduction{h, [], Hidden{}}, NamedProduction{h, [Ref{g, Core.Something{}}, Ref{h, Core.Anything{}}], Hidden{}}]
    case Spec.Positive{} True{}:
      [NamedProduction{h, [Ref{g, Core.Nothing{}}], Rounds{index, link, 1n}}, NamedProduction{h, [Ref{t, Core.Anything{}}], Hidden{}},
       NamedProduction{t, [Ref{g, Core.Something{}}], Rounds{index, link, 1n}}, NamedProduction{t, [Ref{t, Core.Anything{}}, Ref{g, Core.Something{}}], Rounds{index, link, 2n}}]
    case Spec.Positive{} False{}:
      [NamedProduction{h, [Ref{g, Core.Nothing{}}], Hidden{}}, NamedProduction{h, [Ref{g, Core.Something{}}, Ref{t, Core.Anything{}}], Hidden{}},
       NamedProduction{t, [], Hidden{}}, NamedProduction{t, [Ref{g, Core.Something{}}, Ref{t, Core.Anything{}}], Hidden{}}]

# The symbol a bracket stands as in its sequence, and the names it declares.
def bracketSym(kind: Spec.Bracket, +g: Name, +h: Name) -> NamedSym:
  match kind:
    case Spec.Group{}:
      Ref{g, Core.Anything{}}
    case _:
      Ref{h, Core.Anything{}}

def bracketNames(kind: Spec.Bracket, +g: Name, +h: Name, +t: Name) -> +List<Name>:
  match kind:
    case Spec.Group{}:
      [g]
    case Spec.Optional{}:
      [g, h]
    case Spec.Closure{}:
      [g, h]
    case Spec.Positive{}:
      [g, h, t]

def bracketOut(+kind: Spec.Bracket, +left: Bool, +index: Nat, +here: +List<Nat>, alts: Out, rest: Out) -> Out:
  match alts rest:
    case Out{as, +ap, +an, +at, +aok} Out{+rs, +rp, +rn, +rt, +rok}:
      +g = {Group{index, groupPath(kind, here)} : Name}
      +h = {Shape{index, here} : Name}
      +t = {Tail{index, here} : Name}
      Out{bracketSym(kind, g, h) <> rs,
        List.append(&2, NamedProduction, shapeProds(kind, left, g, h, t, index, List.append(&2, Nat, here, [0n, 1n])), List.append(&2, NamedProduction, ap, rp)),
        List.append(&2, Name, bracketNames(kind, g, h, t), List.append(&2, Name, an, rn)),
        Nat.max(at, rt), Bool.and(aok, rok)}

# One alternative of the group at (index, path): its production, then the others'.
def altOut(+index: Nat, +path: +List<Nat>, +a: Nat, alt: Out, rest: Out) -> Out:
  match alt rest:
    case Out{+s, +p, +n, +t, +ok} Out{rs, +rp, +rn, +rt, +rok}:
      Out{[], NamedProduction{Group{index, path}, s, Sequence{index, List.append(&2, Nat, path, [a])}} <> List.append(&2, NamedProduction, p, rp),
        List.append(&2, Name, n, rn), Nat.max(t, rt), Bool.and(ok, rok)}

type Mode is Data:
  MItems{}
  MAlts{}

# One walk for sequences (MItems: the items from `dot` on of the sequence at (index, path))
# and for a group's alternatives (MAlts: alternative `dot` on of the group at (index,
# path)), since Bend has no mutual recursion. `fuel` counts nesting, as in GLL.bend.
def walk(fuel: Nat, mode: Mode, items: +List<Spec.Item>, alts: +List<+List<Spec.Item>>, +left: Bool, +index: Nat, +path: +List<Nat>, +dot: Nat) -> Out:
  match fuel mode items alts:
    case 0n _ _ _:
      Out{[], [], [], 0n, False{}}
    case 1n+(+f) MItems{} Nil{} _:
      emptyOut()
    case 1n+(+f) MItems{} Con{Spec.Sym{Spec.Terminal{+k}}, rest} _:
      consSym(Token{k}, 0n, walk(1n+f, MItems{}, rest, alts, left, index, path, 1n+dot))
    case 1n+(+f) MItems{} Con{Spec.Sym{Spec.Nonterminal{+x}}, rest} _:
      consSym(Ref{Written{x}, Core.Anything{}}, 1n+x, walk(1n+f, MItems{}, rest, alts, left, index, path, 1n+dot))
    case 1n+(+f) MItems{} Con{Spec.Eps{}, rest} _:
      consSym(Ref{Epsilon{}, Core.Anything{}}, 0n, walk(1n+f, MItems{}, rest, alts, left, index, path, 1n+dot))
    case 1n+(+f) MItems{} Con{Spec.Brack{+kind, +inner}, rest} _:
      +here = List.append(&2, Nat, path, [dot])
      bracketOut(kind, left, index, here,
        walk(f, MAlts{}, [], bodyFor(kind, inner), left, index, groupPath(kind, here), 0n),
        walk(1n+f, MItems{}, rest, alts, left, index, path, 1n+dot))
    case 1n+(+f) MAlts{} _ Nil{}:
      emptyOut()
    case 1n+(+f) MAlts{} _ Con{alt, rest}:
      altOut(index, path, dot, walk(f, MItems{}, alt, [], left, index, List.append(&2, Nat, path, [dot]), 0n), walk(1n+f, MAlts{}, items, rest, left, index, path, 1n+dot))

def nestFuel() -> Nat:
  64n

# The productions as written, translated, and everything their brackets add.
type Pass is Data:
  Pass{written: +List<NamedProduction>, added: +List<NamedProduction>, names: +List<Name>, top: Nat, ok: Bool}

def passCons(+lhs: Nat, +index: Nat, o: Out, rest: Pass) -> Pass:
  match o rest:
    case Out{+s, +p, +n, +t, +ok} Pass{+w, +ad, +rn, +rt, +rok}:
      Pass{NamedProduction{Written{lhs}, s, Sequence{index, []}} <> w, List.append(&2, NamedProduction, p, ad), List.append(&2, Name, n, rn), Nat.max(1n+lhs, Nat.max(t, rt)), Bool.and(ok, rok)}

def pass(prods: +List<Spec.Production>, +left: Bool, +index: Nat) -> Pass:
  match prods:
    case Nil{}:
      Pass{[], [], [], 0n, True{}}
    case Con{Spec.Production{+lhs, +rhs}, rest}:
      passCons(lhs, index, walk(nestFuel(), MItems{}, rhs, [], left, index, [], 0n), pass(rest, left, 1n+index))

# ======== PASS 2: NUMBERS ========
#
# Written nonterminals keep their numbers; the new ones are numbered from one past the
# largest written one, in the order they were declared (E first). Productions keep their
# order: those as written first, at their own numbers, then E's, then the added ones.

def natsEq(xs: +List<Nat>, ys: +List<Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+x, xr} Con{+y, yr}:
      Bool.and(Nat.is_eq(x, y), natsEq(xr, yr))
    case _ _:
      False{}

def nameEq(a: Name, b: Name) -> Bool:
  match a b:
    case Written{x} Written{y}:
      Nat.is_eq(x, y)
    case Group{i1, p1} Group{i2, p2}:
      Bool.and(Nat.is_eq(i1, i2), natsEq(p1, p2))
    case Shape{i1, p1} Shape{i2, p2}:
      Bool.and(Nat.is_eq(i1, i2), natsEq(p1, p2))
    case Tail{i1, p1} Tail{i2, p2}:
      Bool.and(Nat.is_eq(i1, i2), natsEq(p1, p2))
    case Epsilon{} Epsilon{}:
      True{}
    case _ _:
      False{}

def positionPick(here: Bool, +later: Nat) -> Nat:
  match here:
    case True{}:
      0n
    case False{}:
      1n+later

def positionOf(+n: Name, names: +List<Name>) -> Nat:
  match names:
    case Nil{}:
      0n
    case Con{+m, rest}:
      positionPick(nameEq(n, m), positionOf(n, rest))

def idOf(n: Name, +names: +List<Name>, +base: Nat) -> Nat:
  match n:
    case Written{+x}:
      x
    case +other:
      Nat.add(base, positionOf(other, names))

def symOf(s: NamedSym, +names: +List<Name>, +base: Nat) -> Core.Sym:
  match s:
    case Token{+k}:
      Core.Terminal{k}
    case Ref{+n, +need}:
      Core.Nonterminal{idOf(n, names, base), need}

def symsOf(ss: +List<NamedSym>, +names: +List<Name>, +base: Nat) -> +List<Core.Sym>:
  match ss:
    case Nil{}:
      []
    case Con{+s, rest}:
      symOf(s, names, base) <> symsOf(rest, names, base)

def prodsOf(ps: +List<NamedProduction>, +names: +List<Name>, +base: Nat) -> +List<Core.Production>:
  match ps:
    case Nil{}:
      []
    case Con{NamedProduction{+lhs, +rhs, origin}, rest}:
      Core.Production{idOf(lhs, names, base), symsOf(rhs, names, base)} <> prodsOf(rest, names, base)

def originsOf(ps: +List<NamedProduction>) -> +List<Origin>:
  match ps:
    case Nil{}:
      []
    case Con{NamedProduction{lhs, rhs, +origin}, rest}:
      origin <> originsOf(rest)

# A translation: the core grammar, where each production came from, and whether the
# nesting fuel lasted (a grammar nested deeper than nestFuel has no translation).
type Translation is Data:
  Translation{grammar: +List<Core.Production>, origins: +List<Origin>, ok: Bool}

def number(p: Pass) -> Translation:
  match p:
    case Pass{+written, +added, +names, +top, +ok}:
      +all = {Epsilon{} <> names : +List<Name>}
      +ps = {List.append(&2, NamedProduction, written, NamedProduction{Epsilon{}, [], Hidden{}} <> added) : +List<NamedProduction>}
      Translation{prodsOf(ps, all, top), originsOf(ps), ok}

def translate(+grammar: +List<Spec.Production>, +left: Bool) -> Translation:
  number(pass(grammar, left, 0n))

# The grammar the parser, pruning and the oracles work on, and Swift's steps come from.
def towardsSwift(+grammar: +List<Spec.Production>) -> Translation:
  translate(grammar, True{})

# The grammar the LL(1) laws work on.
def towardsLL1(+grammar: +List<Spec.Production>) -> Translation:
  translate(grammar, False{})

# ======== THE STEP MAP ========
#
# A core step of the translation towards Swift, as Swift Apus records it: a step of a
# sequence as written keeps its slot; a loop's round is its link step; the steps of shapes
# and of E are not Swift's (they map to nothing). Used by the tests, to compare Swift's
# steps with the twin's.

def originAt(origins: +List<Origin>, q: Nat) -> Origin:
  match origins q:
    case Nil{} _:
      Hidden{}
    case Con{+o, rest} 0n:
      o
    case Con{o, rest} 1n+n:
      originAt(rest, n)

def roundStep(here: Bool, +index: Nat, +link: +List<Nat>, +i: Nat, +k: Nat, +j: Nat) -> Maybe<&2, Spec.Bsr>:
  match here:
    case True{}:
      Some{Spec.Bsr{Spec.Slot{index, link}, i, k, j}}
    case False{}:
      None{}

def stepOf(origin: Origin, +dot: Nat, +i: Nat, +k: Nat, +j: Nat) -> Maybe<&2, Spec.Bsr>:
  match origin:
    case Sequence{+index, +path}:
      Some{Spec.Bsr{Spec.Slot{index, List.append(&2, Nat, path, [dot])}, i, k, j}}
    case Rounds{+index, +link, +d}:
      roundStep(Nat.is_eq(d, dot), index, link, i, k, j)
    case Hidden{}:
      None{}

def toSwift(+origins: +List<Origin>, b: Core.Bsr) -> Maybe<&2, Spec.Bsr>:
  match b:
    case Core.Bsr{+q, +dot, +i, +k, +j}:
      stepOf(originAt(origins, q), dot, i, k, j)

def keep(m: Maybe<&2, Spec.Bsr>, +rest: +List<Spec.Bsr>) -> +List<Spec.Bsr>:
  match m:
    case None{}:
      rest
    case Some{+b}:
      b <> rest

def stepsToSwift(+origins: +List<Origin>, bs: +List<Core.Bsr>) -> +List<Spec.Bsr>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      keep(toSwift(origins, b), stepsToSwift(origins, rest))

def coreOf(t: Translation) -> +List<Core.Production>:
  match t:
    case Translation{+g, o, ok}:
      g

def originsIn(t: Translation) -> +List<Origin>:
  match t:
    case Translation{g, +o, ok}:
      o
