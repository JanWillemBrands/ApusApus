# Apus in Bend

A formally checked specification of EBNF parsing, with a GLL parser whose output
is checked against it. Written in [Bend 2](GUIDE.md).

## What to read

Only two files are trusted. Everything else is either checked by the machine or
there for intuition.

| File | What it is | Read? |
|---|---|---|
| `SPEC.bend` | What parsing means: grammars (EBNF right sides with `( ) [ ] { } < >`), parse trees, `fits`, `leaves`, the steps of a tree as BSR elements, and exact BSR sets | **yes** |
| `LAWS.bend` | Every claim, nothing else | **yes** |
| `EXAMPLES.bend` | The paper's examples, the engine on them, the check catching broken states | for intuition |
| `GLL.bend` | The GLL engine, after tinyGLL and ApusApus | optional: not trusted |
| `CHECK.bend` | The closedness check on the engine's final state, and `checkedSteps` | optional: proven |
| `PROOF.bend` | The gate | run, don't read |
| `PROOF_TREES.bend` | Proofs of the rewriting laws | no |
| `PROOF_GLL.bend` | Proof that the checked parser misses nothing | no |
| `LEMMAS.bend` | Facts about Bool, Nat and lists | no |
| `bnf/` | The earlier BNF specification with a proven CYK parser, frozen | history |

## How to check

```
bend PROOF.bend             # ALL PROOFS CHECK when every law holds
bend PROOF.bend --verdict   # the same, with the Lean-proven kernel
bend EXAMPLES.bend          # the examples
bend bnf/PROOF.bend         # the frozen BNF and CYK work
```

## What is proven

- **Rewriting laws**: each bracket means its usual BNF rewriting, without helper
  nonterminals. `{τ} η` derives what `η` or `(τ) {τ} η` derives, and so on.
- **The checked GLL parser misses nothing** (`gll_every_parse_step`): whenever
  `checkedSteps` hands out a set, every step of every parse tree of the input is
  in it.

## Still to do

- Generalized pruning, which turns a complete set into the exact one.
- `gll_bsr_exact`: the checked parser's pruned set is exactly the steps of the
  parse trees.
