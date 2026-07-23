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

import WOW144.MetricBounds

/-!
# Positive center depth is strictly below diameter

When the center depth is positive, a vertex attaining it lies outside the
center. If its distance to a nearest center vertex were the diameter, that
center vertex would itself be peripheral, forcing radius to equal diameter and
hence every vertex to be central. This contradiction yields
`ecc G G.center + 1 ≤ G.diam`.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [DecidableEq α] [Nontrivial α] in
/-- A positive value of `ecc G S` is attained by a vertex outside `S`. -/
lemma exists_ecc_witness_of_pos_wow144 (S : Set α) (hpos : 0 < ecc G S) :
    ∃ x, x ∉ S ∧ G.distToSet x S = ecc G S := by
  by_cases hout : (Finset.univ.filter (fun v : α => v ∉ S)).Nonempty
  · simp only [ecc]
    rw [dif_pos hout]
    obtain ⟨x, hx, hval⟩ :=
      Finset.mem_image.mp (Finset.max'_mem _ (hout.image _))
    exact ⟨x, (Finset.mem_filter.mp hx).2, hval⟩
  · simp only [ecc] at hpos
    rw [dif_neg hout] at hpos
    omega

omit [DecidableEq α] in
/-- Positive center depth is strictly smaller than the diameter. -/
lemma centerDepth_add_one_le_diam_wow144 (hconn : G.Connected)
    (hpos : 0 < ecc G G.center) :
    ecc G G.center + 1 ≤ G.diam := by
  have hle := centerDepth_le_diam_wow144 (G := G) hconn
  suffices hne : ecc G G.center ≠ G.diam by omega
  intro heq
  obtain ⟨x, hxOut, hx⟩ := exists_ecc_witness_of_pos_wow144
    (G := G) G.center hpos
  obtain ⟨c, hcCenter, hc⟩ := exists_mem_dist_eq_distToSet_wow144
    (G := G) x G.center_nonempty
  have hxc : G.dist x c = G.diam := by omega
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hed : G.edist c x = G.ediam := by
    rw [← (hconn.preconnected c x).coe_dist_eq_edist, G.dist_comm, hxc, diam]
    exact ENat.coe_toNat hfinite
  have hdiamEcc : G.ediam ≤ G.eccent c := by
    calc
      G.ediam = G.edist c x := hed.symm
      _ ≤ G.eccent c := edist_le_eccent
  have hcRadius : G.eccent c = G.radius := (mem_center_iff c).mp hcCenter
  have hradius : G.radius = G.ediam := by
    apply le_antisymm radius_le_ediam
    rw [← hcRadius]
    exact hdiamEcc
  have hcenter : G.center = Set.univ :=
    (center_eq_univ_iff_radius_eq_ediam).2 hradius
  apply hxOut
  rw [hcenter]
  trivial

#print axioms exists_ecc_witness_of_pos_wow144
#print axioms centerDepth_add_one_le_diam_wow144

end SimpleGraph

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Conjecture 144 holds for every connected graph of girth three. -/
theorem conjecture144_of_girth_three
    (G : SimpleGraph α) (hconn : G.Connected) (hg : G.girth = 3) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  by_cases hzero : ecc G G.center = 0
  · exact conjecture144_of_centerDepth_zero G hzero
  have hpos : 0 < ecc G G.center := Nat.pos_of_ne_zero hzero
  have hstrict := centerDepth_add_one_le_diam_wow144 (G := G) hconn hpos
  have htree := diam_add_one_le_largestInducedTreeSize_wow144 (G := G) hconn
  apply conjecture144_of_nat_bound G
  rw [hg]
  omega

#print axioms WOW144.conjecture144_of_girth_three

end WOW144
