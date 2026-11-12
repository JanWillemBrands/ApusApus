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
import ./PROOF_SAVES.bend as ProofSaves
import ./PROOF_LL1.bend as ProofLl1
import ./PROOF_UNAMBIGUOUS.bend as ProofUnambiguous
import ./PROOF_NODEAD.bend as ProofNoDead
import ./PROOF_NODEAD2.bend as ProofNoDead2
import ./PROOF_LL1AT.bend as ProofLl1At

# THE GATE. `bend PROOF.bend` checks every law in LAWS.bend: it prints ALL PROOFS
# CHECK only when each one is proven; `--verdict` checks again with the Lean-proven
# kernel.
#
#   PROOF_TREES.bend  the rewriting laws, about trees and `fits`
#   PROOF_GLL.bend    the checked GLL parser misses no step of any parse tree, also with
#                     prediction (PROOF_PRED, PROOF_ADMIT, PROOF_TABLES, PROOF_SETS)
#   PROOF_ROUNDS.bend the round rule keeps every step of every parse tree
#   PROOF_SAVES.bend  a supported state is within a closed one: predict_saves_work
#   PROOF_LL1.bend    no conflict by the tables means LL(1): tables_ll1_sound
#   PROOF_UNAMBIGUOUS.bend two parse trees of an LL(1) grammar are the same: ll1_unambiguous
#   PROOF_NODEAD2.bend the checked LL(1) parser has no dead wood: ll1_no_dead_wood (on
#                     PROOF_NODEAD.bend, its first stage for grammars without brackets)
#   PROOF_LL1AT.bend  LL(1) at one choice point decides the choice there: ll1_at
#   PROOF_PRUNE.bend  pruning keeps every step of every parse tree
#   PROOF_EXACT.bend  the exact parser's set is exact: gll_bsr_exact
#   PROOF_SPELL.bend  trees built from the exact set spell the input: exact_trees_spell
#   PROOF_PREFER.bend @prefer and @avoid choose exactly the unbeaten trees, among the admissible
#                     ones: prefer_avoid_exact, prefer_avoid_safe
#   PROOF_LOCAL.bend  the phases judge a node by what it reads: holds_local, the swap laws
#   PROOF_SUPPORT.bend a no from the admissible sub-parse leaves no admissible rival
#   PROOF_SUBPARSE.bend what a sub-parse and the exact set say about trees
#   PROOF_GUARD.bend  lookahead, @left and @right keep exactly the admissible trees: guards_exact
#   PROOF_EXTENT.bend @longest and @shortest keep exactly the selected trees, among the unbeaten
#                     ones: extent_exact
#   PROOF_PLUG.bend   a forest swapped into a tree where it keeps phases 1 and 2 leaves the
#                     tree unbeaten, and its steps are the tree's (plugging)
#   FITS.bend         facts about `fits`, one tree and one item at a time
#   LEMMAS.bend       facts about Bool, Nat and lists
