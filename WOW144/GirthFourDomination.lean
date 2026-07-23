import WOW144.GirthFourReplacement
import WOW144.NearestSetDepth

/-!
# Non-dominating diametral paths at girth four

If a diametral geodesic in a girth-four graph is not dominating, choose a
nearest path from a vertex at distance at least two. The boundary vertex either
has a unique path neighbor, or it is an opposite 4-cycle corner; in the latter
case the path-replacement theorem makes the next vertex uniquely attach to a
new diametral geodesic. Either way there is an induced tree on `diameter + 2`
vertices.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [Nontrivial α] in
lemma Walk.girth_four_nondominating_diam_add_two_le_tree_wow144
    {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hdiam : G.dist u v = G.diam)
    (hconn : G.Connected) (hg : 4 ≤ G.girth)
    (hnondom : ∃ x : α,
      2 ≤ G.distToSet x (p.support.toFinset : Set α)) :
    G.diam + 2 ≤ largestInducedTreeSize G := by
  obtain ⟨x, hxDepth⟩ := hnondom
  have hPnonempty : ((p.support.toFinset : Finset α) : Set α).Nonempty :=
    ⟨u, by simp⟩
  obtain ⟨ku, hku, q, hqPath, hq⟩ :=
    hconn.exists_path_length_eq_distToSet_wow144 x hPnonempty
  have hqTwo : 2 ≤ q.length := by
    rw [hq]
    exact hxDepth
  have hkuP : ku ∈ p.support := by simpa using hku
  have hqNotNil : ¬q.Nil := by
    simpa [Walk.not_nil_iff_lt_length] using (show 0 < q.length by omega)
  have hzAdj : G.Adj q.penultimate ku := q.adj_penultimate hqNotNil
  have hzOut : q.penultimate ∉ p.support := by
    have hnot := q.getVert_not_mem_of_length_eq_distToSet_wow144 hq
      (i := q.length - 1) (by omega)
    simpa [Walk.penultimate] using hnot
  by_cases huniq : ∀ ⦃b : α⦄, b ∈ p.support →
      G.Adj q.penultimate b → b = ku
  · exact p.unique_outside_attachment_diam_add_two_le_tree_wow144
      hp hdiam hzOut hkuP hzAdj huniq
  · push_neg at huniq
    obtain ⟨b, hbP, hzb, hbNe⟩ := huniq
    obtain ⟨i, hiEq, hiLe⟩ :=
      Walk.mem_support_iff_exists_getVert.mp hkuP
    obtain ⟨j, hjEq, hjLe⟩ :=
      Walk.mem_support_iff_exists_getVert.mp hbP
    have hzi : G.Adj q.penultimate (p.getVert i) := by
      simpa [hiEq] using hzAdj
    have hzj : G.Adj q.penultimate (p.getVert j) := by
      simpa [hjEq] using hzb
    have hij : i ≠ j := by
      intro hij
      apply hbNe
      calc
        b = p.getVert j := hjEq.symm
        _ = p.getVert i := by rw [hij]
        _ = ku := hiEq
    let w₂ := q.getVert (q.length - 2)
    have hw₂z : G.Adj w₂ q.penultimate := by
      dsimp [w₂, Walk.penultimate]
      have hindex : q.length - 2 + 1 = q.length - 1 := by omega
      simpa only [hindex] using
        q.adj_getVert_succ (i := q.length - 2) (by omega)
    have hw₂Depth :
        G.distToSet w₂ (p.support.toFinset : Set α) = 2 := by
      have hdepth := q.distToSet_getVert_eq_length_sub_of_nearest_wow144
        hconn (by simpa using hku) hq (i := q.length - 2) (by omega)
      dsimp [w₂]
      rw [hdepth]
      omega
    have hw₂Out : w₂ ∉ p.support := by
      have hnot := q.getVert_not_mem_of_length_eq_distToSet_wow144 hq
        (i := q.length - 2) (by omega)
      simpa [w₂] using hnot
    have hw₂NoPathAdj : ∀ ⦃y : α⦄, y ∈ p.support → ¬G.Adj w₂ y := by
      intro y hy hwy
      have hySet : y ∈ (p.support.toFinset : Set α) := by simpa using hy
      have hsetLe := distToSet_le_dist_of_mem_wow144 (G := G) w₂ hySet
      have hdistOne : G.dist w₂ y = 1 := dist_eq_one_iff_adj.mpr hwy
      rw [hw₂Depth, hdistOne] at hsetLe
      omega
    exact p.girth_four_two_level_diam_add_two_le_tree_wow144
      hp hdiam hiLe hjLe hzOut hzi hzj hij hg hw₂z hw₂Out hw₂NoPathAdj

#print axioms Walk.girth_four_nondominating_diam_add_two_le_tree_wow144

end SimpleGraph
