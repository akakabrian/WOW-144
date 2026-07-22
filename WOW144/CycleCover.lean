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

import WOW144.CycleBase
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity

/-!
# Girth cycles that cover the graph

A girth-realizing cycle containing every vertex forces every vertex to have
maximum eccentricity. Consequently the graph is self-centered and the custom
center-depth invariant `ecc G G.center` is zero.

The cycle metric lemmas are locally reproduced from the checked Conjecture 142
development under its Apache-2.0 license.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [Fintype α] [DecidableEq α] in
/-- Every support vertex of a cycle occurs before the closing index. -/
lemma Walk.IsCycle.exists_index_lt_getVert_wow144
    {z x : α} {c : G.Walk z z} (hc : c.IsCycle) (hx : x ∈ c.support) :
    ∃ i : ℕ, i < c.length ∧ c.getVert i = x := by
  obtain ⟨i, hiEq, hiLe⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hiLt : i < c.length
  · exact ⟨i, hiLt, hiEq⟩
  have hiLen : i = c.length := by omega
  have hpos : 0 < c.length := by
    have := hc.three_le_length
    omega
  refine ⟨0, hpos, ?_⟩
  calc
    c.getVert 0 = z := by simp
    _ = c.getVert c.length := by simp
    _ = x := by simpa [hiLen] using hiEq

omit [Fintype α] [DecidableEq α] in
/-- The sum of the three pairwise distances between vertices on a cycle is at
most the cycle length. -/
lemma Walk.IsCycle.sum_three_dist_le_length_wow144
    {z a b d : α} {c : G.Walk z z} (hc : c.IsCycle)
    (ha : a ∈ c.support) (hb : b ∈ c.support) (hd : d ∈ c.support) :
    G.dist a b + G.dist a d + G.dist b d ≤ c.length := by
  obtain ⟨i, hiLt, hi⟩ := hc.exists_index_lt_getVert_wow144 ha
  obtain ⟨j, hjLt, hj⟩ := hc.exists_index_lt_getVert_wow144 hb
  obtain ⟨k, hkLt, hk⟩ := hc.exists_index_lt_getVert_wow144 hd
  have key : ∀ {i j k : ℕ} {a b d : α},
      i < c.length → j < c.length → k < c.length →
      c.getVert i = a → c.getVert j = b → c.getVert k = d →
      i ≤ j → j ≤ k →
      G.dist a b + G.dist a d + G.dist b d ≤ c.length := by
    intro i j k a b d hiLt hjLt hkLt hi hj hk hij hjk
    have hab0 := G.dist_le ((c.drop i).take (j - i))
    have hab : G.dist a b ≤ j - i := by
      simpa [Walk.drop_getVert, Nat.add_sub_of_le hij, hi, hj,
        Walk.take_length, Walk.drop_length,
        Nat.min_eq_left (by omega : j - i ≤ c.length - i)] using hab0
    have hbd0 := G.dist_le ((c.drop j).take (k - j))
    have hbd : G.dist b d ≤ k - j := by
      simpa [Walk.drop_getVert, Nat.add_sub_of_le hjk, hj, hk,
        Walk.take_length, Walk.drop_length,
        Nat.min_eq_left (by omega : k - j ≤ c.length - j)] using hbd0
    have hda0 := G.dist_le ((c.drop k).append (c.take i))
    have hda : G.dist a d ≤ c.length - k + i := by
      have h0 : G.dist d a ≤ c.length - k + i := by
        simpa [Walk.length_append, Walk.drop_length, Walk.take_length,
          Nat.min_eq_left (Nat.le_of_lt hiLt), hi, hk] using hda0
      simpa only [G.dist_comm] using h0
    omega
  rcases le_total i j with hij | hji
  · rcases le_total j k with hjk | hkj
    · exact key hiLt hjLt hkLt hi hj hk hij hjk
    · rcases le_total i k with hik | hki
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hiLt hkLt hjLt hi hk hj hik hkj
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hkLt hiLt hjLt hk hi hj hki hij
  · rcases le_total i k with hik | hki
    · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
        key hjLt hiLt hkLt hj hi hk hji hik
    · rcases le_total j k with hjk | hkj
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hjLt hkLt hiLt hj hk hi hjk hki
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hkLt hjLt hiLt hk hj hi hkj hji

omit [Fintype α] in
/-- A cycle has one distinct support vertex per edge. -/
lemma Walk.IsCycle.card_support_toFinset_eq_length_wow144
    {v : α} {c : G.Walk v v} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have hvTail : v ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  have hfin : c.support.toFinset = c.support.tail.toFinset := by
    rw [c.support_eq_cons, List.toFinset_cons]
    exact Finset.insert_eq_of_mem (by simpa using hvTail)
  rw [hfin, List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
    c.length_support]
  omega

omit [Fintype α] [DecidableEq α] in
/-- Two ambient paths with the same endpoints and support in one induced tree
are equal. -/
lemma IsTree.ambient_path_unique_of_support_subset_wow144
    {S : Finset α} (hT : (G.induce (S : Set α)).IsTree)
    {u v : α} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hpS : ∀ x ∈ p.support, x ∈ (S : Set α))
    (hqS : ∀ x ∈ q.support, x ∈ (S : Set α)) : p = q := by
  have huS : u ∈ (S : Set α) := hpS u p.start_mem_support
  have hvS : v ∈ (S : Set α) := hpS v p.end_mem_support
  let uS : ↥(S : Set α) := ⟨u, huS⟩
  let vS : ↥(S : Set α) := ⟨v, hvS⟩
  let p₀ := p.induce (S : Set α) hpS
  let q₀ := q.induce (S : Set α) hqS
  let pᵢ : (G.induce (S : Set α)).Walk uS vS :=
    p₀.copy (Subtype.ext (by rfl)) (Subtype.ext (by rfl))
  let qᵢ : (G.induce (S : Set α)).Walk uS vS :=
    q₀.copy (Subtype.ext (by rfl)) (Subtype.ext (by rfl))
  have hp₀ : p₀.IsPath := by
    apply (Walk.map_isPath_iff_of_injective
      (p := p₀)
      (f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom)
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).injective).mp
    change (p.induce (S : Set α) hpS).map
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom |>.IsPath
    rw [Walk.map_induce]
    exact hp
  have hq₀ : q₀.IsPath := by
    apply (Walk.map_isPath_iff_of_injective
      (p := q₀)
      (f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom)
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).injective).mp
    change (q.induce (S : Set α) hqS).map
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom |>.IsPath
    rw [Walk.map_induce]
    exact hq
  have hpᵢ : pᵢ.IsPath := by
    dsimp [pᵢ]
    exact (Walk.isPath_copy p₀ (Subtype.ext (by rfl))
      (Subtype.ext (by rfl))).2 hp₀
  have hqᵢ : qᵢ.IsPath := by
    dsimp [qᵢ]
    exact (Walk.isPath_copy q₀ (Subtype.ext (by rfl))
      (Subtype.ext (by rfl))).2 hq₀
  have heq : pᵢ = qᵢ := by
    exact congrArg Subtype.val
      (hT.IsAcyclic.path_unique ⟨pᵢ, hpᵢ⟩ ⟨qᵢ, hqᵢ⟩)
  have hpMap : pᵢ.map (SimpleGraph.Embedding.induce (G := G)
      (S : Set α)).toHom = p := by
    dsimp [pᵢ, p₀]
    simpa using (Walk.map_induce (s := (S : Set α)) p hpS)
  have hqMap : qᵢ.map (SimpleGraph.Embedding.induce (G := G)
      (S : Set α)).toHom = q := by
    dsimp [qᵢ, q₀]
    simpa using (Walk.map_induce (s := (S : Set α)) q hqS)
  rw [← hpMap, ← hqMap, heq]

omit [DecidableEq α] in
/-- Endpoints of a diametral pair have maximum eccentricity. -/
lemma diametral_endpoints_mem_maxEccentricityVertices_wow144 [Nonempty α]
    (hconn : G.Connected) {b w : α} (hbw : G.dist b w = G.diam) :
    b ∈ maxEccentricityVertices G ∧ w ∈ maxEccentricityVertices G := by
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hed : G.edist b w = G.ediam := by
    rw [← (hconn.preconnected b w).coe_dist_eq_edist, hbw, diam]
    exact ENat.coe_toNat hfinite
  constructor
  · change G.eccent b = G.ediam
    exact le_antisymm eccent_le_ediam (by
      calc
        G.ediam = G.edist b w := hed.symm
        _ ≤ G.eccent b := edist_le_eccent)
  · change G.eccent w = G.ediam
    exact le_antisymm eccent_le_ediam (by
      calc
        G.ediam = G.edist b w := hed.symm
        _ = G.edist w b := edist_comm
        _ ≤ G.eccent w := edist_le_eccent)

omit [Fintype α] in
/-- If a girth-realizing cycle covers every vertex, each arc of length at most
half the cycle is geodesic. -/
lemma Walk.IsCycle.take_geodesic_of_vertex_cover_wow144
    {z : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hcover : ∀ x : α, x ∈ c.support) {h : ℕ}
    (hpos : 0 < h) (hhalf : 2 * h ≤ c.length) :
    G.dist z (c.getVert h) = h := by
  have hlt : h < c.length := by omega
  let short : G.Walk z (c.getVert h) := c.take h
  have hshortLen : short.length = h := by
    dsimp [short]
    rw [Walk.take_length, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hdistLe : G.dist z (c.getVert h) ≤ h := by
    simpa [hshortLen] using G.dist_le short
  by_contra hne
  have hdistLt : G.dist z (c.getVert h) < h := by omega
  obtain ⟨p, hpPath, hpLen⟩ := hconn.exists_path_of_dist z (c.getVert h)
  have hdropPos : 0 < (c.drop h).length := by
    rw [Walk.drop_length]
    omega
  have hshortPath : short.IsPath := by
    have hcycSplit : ((c.take h).append (c.drop h)).IsCycle := by
      rw [Walk.append_take_drop_eq]
      exact hc
    dsimp [short]
    exact hcycSplit.isPath_of_append_left
      (Walk.not_nil_iff_lt_length.mpr hdropPos)
  let C := c.support.toFinset
  let P := p.support.toFinset
  let A := short.support.toFinset
  have hcardC : C.card = c.length := by
    simpa [C] using hc.card_support_toFinset_eq_length_wow144
  have hcardP : P.card = p.length + 1 := by
    dsimp [P]
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support]
  have hcardA : A.card = h + 1 := by
    dsimp [A]
    rw [List.toFinset_card_of_nodup hshortPath.support_nodup,
      Walk.length_support, hshortLen]
  have hzr : z ≠ c.getVert h := by
    intro heq
    have hidx : (0 : ℕ) = h := by
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        omega
      · simpa using heq
    omega
  have hpairSub : ({z, c.getVert h} : Finset α) ⊆ P ∩ A := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨by simp [P], by simp [A, short]⟩
    · exact Finset.mem_inter.mpr ⟨by simp [P], by simp [A, short]⟩
  have hcardInter : 2 ≤ (P ∩ A).card := by
    have hle := Finset.card_le_card hpairSub
    simpa [hzr] using hle
  have hcardUnion := Finset.card_union_add_card_inter P A
  have hunionLt : (P ∪ A).card < C.card := by
    rw [hcardC]
    omega
  have hnotSub : ¬C ⊆ P ∪ A := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨erase, hEraseC, hEraseUnion⟩ := Finset.not_subset.mp hnotSub
  have hEraseP : erase ∉ P := by
    intro he
    exact hEraseUnion (Finset.mem_union_left A he)
  have hEraseA : erase ∉ A := by
    intro he
    exact hEraseUnion (Finset.mem_union_right P he)
  have hEraseCycle : erase ∈ c.support := by simpa [C] using hEraseC
  let rot := c.rotate hEraseCycle
  let base := rot.tail.dropLast
  have hbaseCert := hc.erase_vertex_path_certificate_wow144 hEraseCycle hcLength
  change base.IsPath ∧
      base.support.toFinset = c.support.toFinset.erase erase ∧
      (G.induce (base.support.toFinset : Set α)).IsTree ∧
      base.support.toFinset.card = c.length - 1 at hbaseCert
  rcases hbaseCert with ⟨_, hbaseSupport, hbaseTree, _⟩
  have htree :
      (G.induce ((C.erase erase : Finset α) : Set α)).IsTree := by
    change (G.induce ((c.support.toFinset.erase erase : Finset α) : Set α)).IsTree
    rw [← hbaseSupport]
    exact hbaseTree
  have hpS : ∀ y ∈ p.support, y ∈ ((C.erase erase : Finset α) : Set α) := by
    intro y hy
    change y ∈ C.erase erase
    apply Finset.mem_erase.mpr
    constructor
    · intro hye
      subst y
      exact hEraseP (by simpa [P] using hy)
    · simpa [C] using hcover y
  have hshortS : ∀ y ∈ short.support,
      y ∈ ((C.erase erase : Finset α) : Set α) := by
    intro y hy
    change y ∈ C.erase erase
    apply Finset.mem_erase.mpr
    constructor
    · intro hye
      subst y
      exact hEraseA (by simpa [A] using hy)
    · have hyC := (Walk.isSubwalk_take c h).support_subset hy
      simpa [C] using hyC
  have heq := htree.ambient_path_unique_of_support_subset_wow144
    p short hpPath hshortPath hpS hshortS
  have hlenEq := congrArg Walk.length heq
  omega

/-- If a girth-realizing cycle covers every vertex, every vertex is central. -/
lemma Walk.IsCycle.center_eq_univ_of_vertex_cover_wow144
    {z : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hcover : ∀ x : α, x ∈ c.support) :
    G.center = Set.univ := by
  letI : Nonempty α := ⟨z⟩
  let H := c.length / 2
  have hHpos : 0 < H := by
    dsimp [H]
    have := hc.three_le_length
    omega
  have hhalf : 2 * H ≤ c.length := by
    dsimp [H]
    omega
  have hpairUpper : ∀ u v : α, G.dist u v ≤ H := by
    intro u v
    have hs := hc.sum_three_dist_le_length_wow144 (hcover u) (hcover v) (hcover u)
    have hself : G.dist u u = 0 := by simp
    have hsym : G.dist v u = G.dist u v := G.dist_comm
    rw [hself, add_zero, hsym] at hs
    dsimp [H]
    omega
  obtain ⟨b, w, hbw⟩ := G.exists_dist_eq_diam
  have hdiamLe : G.diam ≤ H := by
    rw [← hbw]
    exact hpairUpper b w
  have hzHalf : G.dist z (c.getVert H) = H :=
    hc.take_geodesic_of_vertex_cover_wow144 hcLength hconn hcover hHpos hhalf
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hdiamGe : H ≤ G.diam := by
    rw [← hzHalf]
    exact dist_le_diam hfinite
  have hdiam : G.diam = H := Nat.le_antisymm hdiamLe hdiamGe
  have hperipheral : ∀ u : α, u ∈ maxEccentricityVertices G := by
    intro u
    have hu : u ∈ c.support := hcover u
    let rot := c.rotate hu
    have hrotCycle : rot.IsCycle := by
      dsimp [rot]
      exact hc.rotate hu
    have hrotLength : rot.length = G.girth := by
      dsimp [rot]
      exact (c.length_rotate_wow144 hu).trans hcLength
    have hrotCover : ∀ x : α, x ∈ rot.support := by
      intro x
      dsimp [rot]
      exact (c.mem_support_rotate_iff hu).mpr (hcover x)
    have hrotHalf : 2 * H ≤ rot.length := by
      rw [hrotLength, ← hcLength]
      exact hhalf
    have hur : G.dist u (rot.getVert H) = H :=
      hrotCycle.take_geodesic_of_vertex_cover_wow144
        hrotLength hconn hrotCover hHpos hrotHalf
    have hdiamPair : G.dist u (rot.getVert H) = G.diam := by
      rw [hur, hdiam]
    exact (diametral_endpoints_mem_maxEccentricityVertices_wow144
      hconn hdiamPair).1
  have hall : ∀ u : α, G.eccent u = G.ediam := by
    intro u
    exact hperipheral u
  have hradius : G.radius = G.ediam :=
    (radius_eq_ediam_iff).2 ⟨G.ediam, hall⟩
  exact (center_eq_univ_iff_radius_eq_ediam).2 hradius

/-- A girth-realizing cycle that covers every vertex has center depth zero. -/
lemma Walk.IsCycle.centerDepth_eq_zero_of_vertex_cover_wow144
    {z : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hcover : ∀ x : α, x ∈ c.support) :
    ecc G G.center = 0 := by
  have hcenter := hc.center_eq_univ_of_vertex_cover_wow144 hcLength hconn hcover
  rw [hcenter]
  unfold ecc
  simp

#print axioms Walk.IsCycle.center_eq_univ_of_vertex_cover_wow144
#print axioms Walk.IsCycle.centerDepth_eq_zero_of_vertex_cover_wow144

end SimpleGraph
