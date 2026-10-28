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


If you agree, the order would be:
1. slot navigation and the engine;
2. checking it on the paper's examples;
3. the closedness checker and its proof;
4. the generalized pruning;
5. gll_bsr_exact.


Idea	Verdict	Why
Check Oracle phase 1 against the exact set	do first	Export the yields after phase 1 instead of the raw ones; every case should then Agree. That tests the claim behind phase 2: "every surviving yield participates in at least one complete derivation". It's test code only, on what we already have.
Settle empty rounds	do, as the first Oracle law	It decides which trees the Oracle chooses from. Under our principle it is an Oracle filter: "no empty rounds", with a law that it never removes the last parse. It's the simplest possible example of an Oracle law.
Exporter: "" inside a sequence	do, cheap	3 of the 5 refusals; more test tables come within reach.
Polynomial certificate for "no dead wood"	probably soon	Oracle examples are ambiguous by nature, and the exact parser blew up at n = 8 on the torture grammar. Only needed if the Oracle test cases are too big for it.
Indexed sets, fast checker	when needed	only if Bend run time becomes the bottleneck
Algorithm-independent certificate, parallel engines, fuel law	park	off the Oracle path
Per-file TaskGroup experiment	optional	cheap and useful for ApusApus itself, but unrelated to the Oracle
