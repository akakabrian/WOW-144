/-
Copyright 2026 The WOW-144 Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import WOW144.Geodesic
import WOW144.NearestCycle

/-!
# Small-girth center-depth-one cases

Center depth one rules out complete graphs and therefore forces diameter at
least two. When the girth is three, a diametral geodesic supplies the required
three-vertex induced tree. At girth four, diameter two would force a universal
center vertex, which creates a triangle with an edge of the four-cycle.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [Fintype α] [DecidableEq α] in
/-- Closing a path through a vertex outside its support gives a cycle. -/
private lemma Walk.IsPath.concat_two_isCycle_small_wow144
    {a b x : α} {p : G.Walk a b} (hp : p.IsPath) (hab : a ≠ b)
    (hx : x ∉ p.support) (hbx : G.Adj b x) (hxa : G.Adj x a) :
    ((p.concat hbx).concat hxa).IsCycle := by
  have hpx : (p.concat hbx).IsPath := hp.concat hx hbx
  rw [← Walk.isCycle_reverse, Walk.reverse_concat, Walk.cons_isCycle_iff]
  refine ⟨(Walk.isPath_reverse_iff _).2 hpx, ?_⟩
  intro he
  have he' : s(x, a) ∈ (p.concat hbx).edges := by
    have he0 : s(a, x) ∈ (p.concat hbx).edges := by
      simpa only [Walk.edges_reverse, List.mem_reverse] using he
    rw [Sym2.eq_swap]
    exact he0
  have ha : a = (p.concat hbx).penultimate := hpx.eq_penultimate_of_mem_edges he'
  exact hab (by simpa using ha)

omit [Fintype α] [DecidableEq α] in
/-- A four-cycle contains an edge avoiding any prescribed vertex. -/
lemma Walk.IsCycle.exists_adj_avoiding_of_length_four_wow144
    {z x : α} {c : G.Walk z z} (hc : c.IsCycle) (hlen : c.length = 4) :
    ∃ u v, u ≠ x ∧ v ≠ x ∧ G.Adj u v := by
  have h01 : G.Adj (c.getVert 0) (c.getVert 1) :=
    c.adj_getVert_succ (by omega)
  have h12 : G.Adj (c.getVert 1) (c.getVert 2) :=
    c.adj_getVert_succ (by omega)
  have h23 : G.Adj (c.getVert 2) (c.getVert 3) :=
    c.adj_getVert_succ (by omega)
  have h02 : c.getVert 0 ≠ c.getVert 2 := by
    intro heq
    have hi : (0 : ℕ) = 2 := by
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        omega
      · exact heq
    omega
  have h13 : c.getVert 1 ≠ c.getVert 3 := by
    intro heq
    have hi : (1 : ℕ) = 3 := by
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        omega
      · exact heq
    omega
  by_cases hx0 : x = c.getVert 0
  · refine ⟨c.getVert 1, c.getVert 2, ?_, ?_, h12⟩
    · intro h
      exact h01.ne (hx0.symm.trans h.symm)
    · intro h
      exact h02 (hx0.symm.trans h.symm)
  · by_cases hx1 : x = c.getVert 1
    · refine ⟨c.getVert 2, c.getVert 3, ?_, ?_, h23⟩
      · intro h
        exact h12.ne (hx1.symm.trans h.symm)
      · intro h
        exact h13 (hx1.symm.trans h.symm)
    · exact ⟨c.getVert 0, c.getVert 1, Ne.symm hx0, Ne.symm hx1, h01⟩

end SimpleGraph

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [DecidableEq α] [Nontrivial α] in
/-- Center depth one implies that not every vertex is central. -/
lemma center_ne_univ_of_centerDepth_one (G : SimpleGraph α)
    (hq : ecc G G.center = 1) : G.center ≠ Set.univ := by
  intro hcenter
  rw [hcenter] at hq
  simp [ecc] at hq

omit [DecidableEq α] in
/-- A connected graph of center depth one has diameter at least two. -/
lemma two_le_diam_of_centerDepth_one (G : SimpleGraph α) (hconn : G.Connected)
    (hq : ecc G G.center = 1) : 2 ≤ G.diam := by
  have hdiam0 : G.diam ≠ 0 := (connected_iff_diam_ne_zero.mp hconn)
  have hnotTop : G ≠ ⊤ := by
    intro htop
    have hcenter : G.center = Set.univ := by simpa [htop] using
      (center_top : (⊤ : SimpleGraph α).center = Set.univ)
    exact center_ne_univ_of_centerDepth_one G hq hcenter
  have hdiam1 : G.diam ≠ 1 := by
    intro h
    exact hnotTop (diam_eq_one.mp h)
  omega

omit [DecidableEq α] in
/-- At center depth one and girth four, the diameter is at least three. -/
lemma three_le_diam_of_centerDepth_one_girth_four
    (G : SimpleGraph α) (hconn : G.Connected)
    (hq : ecc G G.center = 1) (hg : G.girth = 4) : 3 ≤ G.diam := by
  have htwo := two_le_diam_of_centerDepth_one G hconn hq
  by_contra hnot
  have hdiam : G.diam = 2 := by omega
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hed : G.ediam = (2 : ℕ∞) := by
    rw [← ENat.coe_toNat hfinite, ← diam, hdiam]
    simp
  have hcenterNe : G.center ≠ Set.univ := center_ne_univ_of_centerDepth_one G hq
  obtain ⟨centerV, hcenterV⟩ := G.center_nonempty
  have hcenterUniversal : ∀ v : α, centerV ≠ v → G.Adj centerV v := by
    intro v hcv
    by_contra hnadj
    have hpos : 0 < G.dist centerV v := hconn.pos_dist_of_ne hcv
    have hle : G.dist centerV v ≤ 2 := by
      have := dist_le_diam hfinite (u := centerV) (v := v)
      simpa [hdiam] using this
    have hneOne : G.dist centerV v ≠ 1 := by
      intro hdist
      exact hnadj (dist_eq_one_iff_adj.mp hdist)
    have hdist : G.dist centerV v = 2 := by omega
    have heccGe : (2 : ℕ∞) ≤ G.eccent centerV := by
      calc
        (2 : ℕ∞) = G.edist centerV v := by
          rw [← (hconn.preconnected centerV v).coe_dist_eq_edist, hdist]
          simp
        _ ≤ G.eccent centerV := edist_le_eccent
    have hcRadius : G.eccent centerV = G.radius :=
      (mem_center_iff centerV).mp hcenterV
    have hrGe : (2 : ℕ∞) ≤ G.radius := by simpa [hcRadius] using heccGe
    apply hcenterNe
    rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff]
    apply le_antisymm
    · calc
        G.eccent u ≤ G.ediam := eccent_le_ediam
        _ = (2 : ℕ∞) := hed
        _ ≤ G.radius := hrGe
    · exact radius_le_eccent
  have hcyc : ¬G.IsAcyclic := by
    intro hacyc
    have := hacyc.girth_eq_zero
    omega
  obtain ⟨z, cyc, hcycWalk, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcycLength : cyc.length = 4 := by omega
  obtain ⟨u, v, huCenter, hvCenter, huv⟩ :=
    hcycWalk.exists_adj_avoiding_of_length_four_wow144
      (x := centerV) hcycLength
  have hcu : G.Adj centerV u := hcenterUniversal u huCenter.symm
  have hcv : G.Adj centerV v := hcenterUniversal v hvCenter.symm
  have hcenterOut : centerV ∉ huv.toWalk.support := by
    simp only [SimpleGraph.Adj.toWalk, Walk.support_cons, Walk.support_nil,
      List.mem_cons, not_or]
    exact ⟨Ne.symm huCenter, ⟨Ne.symm hvCenter, by simp⟩⟩
  have huvPath : huv.toWalk.IsPath := by
    apply Walk.IsPath.mk'
    simp [huv.ne]
  have htri : ((huv.toWalk.concat hcv.symm).concat hcu).IsCycle :=
    huvPath.concat_two_isCycle_small_wow144 huv.ne hcenterOut hcv.symm hcu
  have hgLe := G.girth_le_length htri
  rw [hg] at hgLe
  norm_num at hgLe

/-- Conjecture 144 holds at center depth one when the girth is three. -/
theorem conjecture144_of_centerDepth_one_girth_three
    (G : SimpleGraph α) (hconn : G.Connected)
    (hq : ecc G G.center = 1) (hg : G.girth = 3) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have hdiam := two_le_diam_of_centerDepth_one G hconn hq
  have htree := diam_add_one_le_largestInducedTreeSize_wow144 (G := G) hconn
  apply conjecture144_of_nat_bound G
  rw [hq, hg]
  omega

/-- Conjecture 144 holds at center depth one when the girth is four. -/
theorem conjecture144_of_centerDepth_one_girth_four
    (G : SimpleGraph α) (hconn : G.Connected)
    (hq : ecc G G.center = 1) (hg : G.girth = 4) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have hdiam := three_le_diam_of_centerDepth_one_girth_four G hconn hq hg
  have htree := diam_add_one_le_largestInducedTreeSize_wow144 (G := G) hconn
  apply conjecture144_of_nat_bound G
  rw [hq, hg]
  omega

#print axioms WOW144.conjecture144_of_centerDepth_one_girth_three
#print axioms WOW144.conjecture144_of_centerDepth_one_girth_four

end WOW144
