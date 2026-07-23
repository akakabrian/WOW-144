import WOW144.GeodesicExtension
import WOW144.GeodesicNeighbor

/-!
# The girth-four path-replacement construction

If `z` is adjacent to two vertices of a diametral geodesic and `w` is one layer
farther from the geodesic, girth four forces the two path neighbors to be the
ends of a length-two segment. Replacing the middle path vertex by `z` preserves
the diameter, and `w` is then uniquely attached to the replacement geodesic.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [Fintype α] [Nontrivial α] in
/-- A distance-two vertex behind an opposite 4-cycle corner extends a
diametral geodesic to an induced tree on `diameter + 2` vertices. -/
lemma Walk.girth_four_two_level_diam_add_two_le_tree_wow144
    {u v z w : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hdiam : G.dist u v = G.diam)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hzOut : z ∉ p.support)
    (hzi : G.Adj z (p.getVert i)) (hzj : G.Adj z (p.getVert j))
    (hij : i ≠ j) (hg : 4 ≤ G.girth)
    (hwz : G.Adj w z) (hwOut : w ∉ p.support)
    (hwNoPathAdj : ∀ ⦃y : α⦄, y ∈ p.support → ¬G.Adj w y) :
    G.diam + 2 ≤ largestInducedTreeSize G := by
  have key : ∀ {a b : ℕ}, a ≤ p.length → b ≤ p.length → a + 2 = b →
      G.Adj z (p.getVert a) → G.Adj z (p.getVert b) →
      G.diam + 2 ≤ largestInducedTreeSize G := by
    intro a b ha hb hab hza hzb
    let replacement : G.Walk u v :=
      (((p.take a).concat hza.symm).concat hzb).append (p.drop b)
    have hreplacementLength : replacement.length = p.length := by
      dsimp [replacement]
      rw [Walk.length_append, Walk.length_concat, Walk.length_concat,
        Walk.take_length, Walk.drop_length, Nat.min_eq_left ha]
      omega
    have hreplacementDist : replacement.length = G.dist u v :=
      hreplacementLength.trans hp
    have htakeSub : ∀ ⦃y : α⦄, y ∈ (p.take a).support → y ∈ p.support :=
      (Walk.isSubwalk_take p a).support_subset
    have hdropSub : ∀ ⦃y : α⦄, y ∈ (p.drop b).support → y ∈ p.support :=
      (Walk.isSubwalk_drop p b).support_subset
    have hsupport : ∀ ⦃y : α⦄, y ∈ replacement.support →
        y = z ∨ y ∈ p.support := by
      intro y hy
      have hy' :
          y ∈ (p.take a).support ∨ y = z ∨ y = p.getVert b ∨
            y ∈ (p.drop b).support := by
        simpa [replacement, or_assoc] using hy
      rcases hy' with hyTake | rfl | rfl | hyDrop
      · exact Or.inr (htakeSub hyTake)
      · exact Or.inl rfl
      · exact Or.inr (p.getVert_mem_support b)
      · exact Or.inr (hdropSub hyDrop)
    have hwReplacement : w ∉ replacement.support := by
      intro hw
      rcases hsupport hw with hwEq | hwP
      · exact hwz.ne hwEq
      · exact hwOut hwP
    have hzReplacement : z ∈ replacement.support := by
      simp [replacement]
    have hwUnique : ∀ ⦃y : α⦄, y ∈ replacement.support →
        G.Adj w y → y = z := by
      intro y hy hwy
      rcases hsupport hy with rfl | hyP
      · rfl
      · exact (hwNoPathAdj hyP hwy).elim
    exact replacement.unique_outside_attachment_diam_add_two_le_tree_wow144
      hreplacementDist hdiam hwReplacement hzReplacement hwz hwUnique
  rcases p.geodesic_distinct_neighbor_indices_gap_two_wow144
      hp hi hj hzOut hzi hzj hij hg with hijGap | hjiGap
  · exact key hi hj hijGap hzi hzj
  · exact key hj hi hjiGap hzj hzi

#print axioms Walk.girth_four_two_level_diam_add_two_le_tree_wow144

end SimpleGraph
