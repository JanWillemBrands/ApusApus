
# A step of the walk that is the target, ending at fin: the token at fin is in the context.
law at_fits:
  for +grammar: +List<Spec.Production>
  for +t: Gll.Tables
  for +input: +List<Nat>
  for +index: Nat
  for +rpath: +List<Nat>
  for +prefix: +List<Nat>
  for +d: Nat
  for +i: Nat
  for +k: Nat
  for +e: Nat
  for +fin: Nat
  for +index0: Nat
  for +prefix0: +List<Nat>
  for +i0: Nat
  for +k0: Nat
  for +j0: Nat
  for +rpath1: +List<Nat>
  for +same: {Spec.at(index0, prefix0, List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0)), i0, k0, j0) == Spec.at(index, prefix, d, i, k, e) : Spec.Bsr}
  for +eFin: {e == fin : Nat}
  for +pEq: {prefix == Gll.reverseOnto(rpath, []) : +List<Nat>}
  for +ctxF: {Pr.ctxOk(Gll.Predict{t}, grammar, input, index, rpath, fin) == True{} : Bool}
  for +rEq: {Gll.reverseOnto(rpath1, []) == prefix0 : +List<Nat>}
  Fits(grammar, t, input, index0, rpath1, j0)

def at_fits(grammar, t, input, index, rpath, prefix, d, i, k, e, fin, index0, prefix0, i0, k0, j0, rpath1, same, eFin, pEq, ctxF, rEq):
  +len0 = List.length(&2, Spec.Item, Spec.sequenceAt(grammar, index0, prefix0))
  +target = Spec.at(index0, prefix0, len0, i0, k0, j0)
  +here = Spec.at(index, prefix, d, i, k, e)
  +eIndex = Equal.cong(Spec.Bsr, Nat, v => bsrIndex(v), target, here, same)
  +ePath = Equal.cong(Spec.Bsr, +List<Nat>, v => bsrPath(v), target, here, same)
  +eEnd = Equal.cong(Spec.Bsr, Nat, v => bsrEnd(v), target, here, same)
  +ePrefix = Equal.trans(+List<Nat>, prefix0, initOf(List.append(&2, Nat, prefix0, [len0])), prefix, Equal.sym(+List<Nat>, initOf(List.append(&2, Nat, prefix0, [len0])), prefix0, init_snoc(prefix0, len0)),
    Equal.trans(+List<Nat>, initOf(List.append(&2, Nat, prefix0, [len0])), initOf(List.append(&2, Nat, prefix, [d])), prefix, Equal.cong(+List<Nat>, +List<Nat>, v => initOf(v), List.append(&2, Nat, prefix0, [len0]), List.append(&2, Nat, prefix, [d]), ePath), init_snoc(prefix, d)))
  +j0Fin = Equal.trans(Nat, j0, e, fin, eEnd, eFin)
  +rSame = reverse_injective(rpath1, rpath, Equal.trans(+List<Nat>, Gll.reverseOnto(rpath1, []), prefix0, Gll.reverseOnto(rpath, []), rEq, Equal.trans(+List<Nat>, prefix0, prefix, Gll.reverseOnto(rpath, []), ePrefix, pEq)))
  Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, j0), Gll.contextAfter(grammar, t, index0, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index0, rpath1)), True{},
    Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, v), Gll.contextAfter(grammar, t, index0, rpath1)), j0, fin, j0Fin),
    Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index0, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath1)), True{},
      Equal.cong(Nat, Bool, v => Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, v, rpath1)), index0, index, eIndex),
      Equal.trans(Bool, Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath1)), Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, rpath)), True{},
        Equal.cong(+List<Nat>, Bool, v => Gll.lsHas(List.get(&2, Nat, input, fin), Gll.contextAfter(grammar, t, index, v)), rpath1, rpath, rSame), ctxF)))
