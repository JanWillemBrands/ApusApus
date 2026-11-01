import Base
import ./LAWS.bend as Laws
import ./PROOF_TREES.bend as ProofTrees
import ./PROOF_GLL.bend as ProofGll
import ./PROOF_PRUNE.bend as ProofPrune
import ./PROOF_EXACT.bend as ProofExact
import ./PROOF_SPELL.bend as ProofSpell
import ./PROOF_PREFER.bend as ProofPrefer
import ./PROOF_GUARD.bend as ProofGuard
import ./PROOF_EXTENT.bend as ProofExtent
import ./PROOF_SUPPORT.bend as ProofSupport
import ./PROOF_LOCAL.bend as ProofLocal

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
#   PROOF_PREFER.bend @prefer and @avoid choose exactly the unbeaten trees, among the admissible
#                     ones: prefer_avoid_exact, prefer_avoid_safe
#   PROOF_LOCAL.bend  the phases judge a node by what it reads: holds_local, the swap laws
#   PROOF_SUPPORT.bend a no from the admissible sub-parse leaves no admissible rival
#   PROOF_SUBPARSE.bend what a sub-parse and the exact set say about trees
#   PROOF_GUARD.bend  lookahead, @left and @right keep exactly the admissible trees: guards_exact
#   PROOF_EXTENT.bend @longest and @shortest keep exactly the best-extent trees: extent_exact
#   FITS.bend         facts about `fits`, one tree and one item at a time
#   LEMMAS.bend       facts about Bool, Nat and lists
