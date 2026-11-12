# Generated proofs

Some proof files in `Bend/` are too long and repetitive to write by hand. Each one has a folder
here with its generator scripts (Python) and its hand-written parts, and a `parts.txt` that says
which scripts to run and which parts make up the file, in order.

    python3 Bend/gen/build.py --check-all            # does every folder still give its file?
    python3 Bend/gen/build.py PROOF_NODEAD2 --check  # one folder
    python3 Bend/gen/build.py PROOF_NODEAD2          # rebuild Bend/PROOF_NODEAD2.bend

To change a generated proof, change its script or part here, rebuild, and check the proof with
`bend PROOF.bend` (and `--verdict`). Do not edit the generated `Bend/*.bend` file itself: the next
rebuild would undo it, and `--check-all` reports the difference.

| Folder | Builds | Generators |
|---|---|---|
| `PROOF_TABLES` | `nul_sound`, `first_sound` | `nul.py`, `first.py` |
| `PROOF_LL1` | `tables_ll1_sound` | `walk.py` (the follow walk), `c3.py`, `c4.py` |
| `PROOF_UNAMBIGUOUS` | `ll1_unambiguous` | `p2.py`, `cmp.py` (comparing two forests) |
| `PROOF_NODEAD` | `ll1_no_dead_wood_bnf` | `n2.py`, `n4.py`, `n6.py`, `n7.py` |
| `PROOF_NODEAD2` | `ll1_no_dead_wood` | `m*.py`; `m11b.py` reads `../../PROOF_NODEAD.bend` |
| `PROOF_LL1AT` | `ll1_at` | `a.py` … `d.py` (shared text in `common.py`) |

The other proof files in `Bend/` are written by hand.
