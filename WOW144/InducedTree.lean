import FormalConjectures.WrittenOnTheWallII.GraphConjecture144

/-!
# Explicit induced-tree witnesses

Connects a concrete finite induced tree to the upstream `largestInducedTreeSize` invariant.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [DecidableEq α] in
/-- Every explicit finite induced tree is bounded by `largestInducedTreeSize`.

This is proved directly from the authoritative `sSup` definition, without using any
other WOW II conjecture or an upstream proof splice. -/
lemma finset_card_le_largestInducedTreeSize {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    intro n hn
    rcases hn with ⟨t, rfl, _⟩
    exact Finset.card_le_univ t
  · exact ⟨s, rfl, hs⟩

#print axioms finset_card_le_largestInducedTreeSize

end SimpleGraph
