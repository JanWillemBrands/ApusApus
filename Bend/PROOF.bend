import Base
import ./LAWS.bend as Laws
import ./PROOF_TREES.bend as ProofTrees
import ./PROOF_GLL.bend as ProofGll

# THE GATE. `bend PROOF.bend` checks every law in LAWS.bend: it prints ALL PROOFS
# CHECK only when each one is proven; `--verdict` checks again with the Lean-proven
# kernel.
#
#   PROOF_TREES.bend  the rewriting laws, about trees and `fits`
#   PROOF_GLL.bend    the checked GLL parser misses no step of any parse tree
#   LEMMAS.bend       facts about Bool, Nat and lists
