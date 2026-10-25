Step	Grammar	What you learn in Bend
0	one terminal 'a' (done)	laws, {==} proofs
1	a sequence of terminals	recursion on lists, induction
2	alternatives	Bool reasoning, case analysis
3	non-recursive nonterminals	grammar as a datatype, Derives as a type
4	recursive binary-form grammar plus CYK	termination, soundness and completeness, parallel calls
5	EBNF to BNF	proving that two languages are equal
6	GLL	fuel arguments, the worklist, staying close to Apus


Proposed low-hanging fruit, in order

1. Option A: retire the recognizer laws and CYK soundness (−700 lines, one law family).
2. Generalize embedded to grammar slots, using Scott's definition, while it's still cheap.
3. Adopt good trees as the specification for cyclic grammars, before step 4b.
4. Split SPEC.bend from LAWS.bend􀰓.
5. Later: an ambiguity law, and deciding validation versus proof for grammar transformations.
