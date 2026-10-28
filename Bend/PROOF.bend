import Base
import ./LAWS.bend as Laws
import ./PROOF_TREES.bend as ProofTrees
import ./PROOF_GLL.bend as ProofGll
import ./PROOF_PRUNE.bend as ProofPrune
import ./PROOF_EXACT.bend as ProofExact
import ./PROOF_SPELL.bend as ProofSpell

# THE GATE. `bend PROOF.bend` checks every law in LAWS.bend: it prints ALL PROOFS
# CHECK only when each one is proven; `--verdict` checks again with the Lean-proven
# kernel.
#
#   PROOF_TREES.bend  the rewriting laws, about trees and `fits`
#   PROOF_GLL.bend    the checked GLL parser misses no step of any parse tree
#   PROOF_ROUNDS.bend the round rule keeps every step of every parse tree
#   PROOF_PRUNE.bend  pruning keeps every step of every parse tree
#   PROOF_EXACT.bend  the exact parser's set is exact: gll_bsr_exact
#   PROOF_SPELL.bend  trees built from the exact set spell the input: exact_trees_spell
#   FITS.bend         facts about `fits`, one tree and one item at a time
#   LEMMAS.bend       facts about Bool, Nat and lists
