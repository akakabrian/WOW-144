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

import WOW144.CycleAttachment
import WOW144.CycleCover

/-!
# Nearest descents to a shortest cycle

A nearest path from an outside vertex to a girth-realizing cycle reaches the
cycle through a vertex with a unique cycle neighbor when the girth is at least
five. Combined with the cycle-cover theorem, this proves Conjecture 144 for
center depth one in that girth range.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [DecidableEq α] in
/-- A member of a finite target set bounds distance to that set. -/
lemma distToSet_le_dist_of_mem_wow144 {S : Set α} (x : α) {s : α} (hs : s ∈ S) :
    G.distToSet x S ≤ G.dist x s := by
  unfold distToSet
  split_ifs with h
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Set.mem_toFinset.mpr hs))
  · exact Nat.zero_le _

omit [DecidableEq α] in
/-- Distance to a nonempty finite target set is attained. -/
lemma exists_mem_dist_eq_distToSet_wow144 {S : Set α} (x : α) (hS : S.Nonempty) :
    ∃ s ∈ S, G.distToSet x S = G.dist x s := by
  have hSf : S.toFinset.Nonempty := Set.toFinset_nonempty.mpr hS
  unfold distToSet
  rw [dif_pos hSf]
  have hm := Finset.min'_mem (S.toFinset.image fun s => G.dist x s)
    (Finset.Nonempty.image hSf _)
  rcases Finset.mem_image.mp hm with ⟨s, hs, heq⟩
  refine ⟨s, Set.mem_toFinset.mp hs, ?_⟩
  exact heq.symm

omit [DecidableEq α] in
/-- A connected graph has a geodesic from any vertex to a nearest member of a
nonempty target set. -/
lemma Connected.exists_path_length_eq_distToSet_wow144
    (hconn : G.Connected) (u : α) {S : Set α} (hS : S.Nonempty) :
    ∃ s ∈ S, ∃ p : G.Walk u s,
      p.IsPath ∧ p.length = G.distToSet u S := by
  obtain ⟨s, hs, hdist⟩ := exists_mem_dist_eq_distToSet_wow144 (G := G) u hS
  obtain ⟨p, hpPath, hpLength⟩ := hconn.exists_path_of_dist u s
  exact ⟨s, hs, p, hpPath, hpLength.trans hdist.symm⟩

omit [DecidableEq α] in
/-- A vertex before the endpoint of a nearest-set walk is outside the target. -/
lemma Walk.getVert_not_mem_of_length_eq_distToSet_wow144
    {S : Set α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.distToSet u S) {i : ℕ} (hi : i < p.length) :
    p.getVert i ∉ S := by
  intro hiS
  have hsetLe := distToSet_le_dist_of_mem_wow144 (G := G) u hiS
  have hdistLe : G.dist u (p.getVert i) ≤ (p.take i).length := G.dist_le (p.take i)
  have htake : (p.take i).length = i := by
    rw [Walk.take_length, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hbad : p.length ≤ i := by
    calc
      p.length = G.distToSet u S := hp
      _ ≤ G.dist u (p.getVert i) := hsetLe
      _ ≤ (p.take i).length := hdistLe
      _ = i := htake
  omega

omit [Fintype α] [DecidableEq α] in
/-- Closing a path through a vertex outside its support gives a cycle. -/
private lemma Walk.IsPath.concat_two_isCycle_wow144
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
/-- If a cycle realizes the girth and has length at least five, an outside
vertex has at most one neighbor on the cycle. -/
theorem Walk.IsCycle.outside_neighbor_unique_of_length_eq_girth_wow144
    {v a b x : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth)
    (hx : x ∉ c.support) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b := by
  by_contra hab
  let r : G.Walk a a := c.rotate ha
  have hrCycle : r.IsCycle := hc.rotate ha
  have hbR : b ∈ r.support := (c.mem_support_rotate_iff ha).2 hb
  have hxR : x ∉ r.support := fun hxmem => hx ((c.mem_support_rotate_iff ha).1 hxmem)
  let p : G.Walk a b := r.takeUntil b hbR
  let q : G.Walk b a := r.dropUntil b hbR
  have hpPath : p.IsPath := hrCycle.isPath_takeUntil hbR
  have hqPath : q.IsPath := by
    apply Walk.IsCycle.isPath_of_append_right (p := p) (q := q) (Walk.not_nil_of_ne hab)
    simpa [p, q] using hrCycle
  have hxP : x ∉ p.support := fun hxmem => hxR (r.support_takeUntil_subset hbR hxmem)
  have hxQ : x ∉ q.support := fun hxmem => hxR (r.support_dropUntil_subset hbR hxmem)
  have hpCycle : ((p.concat hxb.symm).concat hxa).IsCycle :=
    hpPath.concat_two_isCycle_wow144 hab hxP hxb.symm hxa
  have hqCycle : ((q.concat hxa.symm).concat hxb).IsCycle :=
    hqPath.concat_two_isCycle_wow144 (Ne.symm hab) hxQ hxa.symm hxb
  have hpBound : G.girth ≤ p.length + 2 := by
    simpa only [Walk.length_concat] using G.girth_le_length hpCycle
  have hqBound : G.girth ≤ q.length + 2 := by
    simpa only [Walk.length_concat] using G.girth_le_length hqCycle
  have hrLength : r.length = c.length := by
    dsimp [r, Walk.rotate]
    rw [Walk.length_append, add_comm, ← Walk.length_append, c.take_spec ha]
  have hsplit : p.length + q.length = G.girth := by
    have h0 := congrArg Walk.length (r.take_spec hbR)
    have h1 : p.length + q.length = r.length := by
      simpa only [Walk.length_append, p, q] using h0
    omega
  omega

omit [Fintype α] [DecidableEq α] in
/-- Every vertex of a cycle has a different support vertex. -/
lemma Walk.IsCycle.exists_support_ne_wow144
    {z a : α} {c : G.Walk z z} (hc : c.IsCycle) (ha : a ∈ c.support) :
    ∃ b ∈ c.support, b ≠ a := by
  let r : G.Walk a a := c.rotate ha
  have hrCycle : r.IsCycle := hc.rotate ha
  have hbR : r.snd ∈ r.support := r.getVert_mem_support 1
  have hbC : r.snd ∈ c.support := (c.mem_support_rotate_iff ha).1 hbR
  exact ⟨r.snd, hbC, (r.adj_snd hrCycle.not_nil).ne.symm⟩

end SimpleGraph

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Conjecture 144 holds at center depth one when the girth is at least five. -/
theorem conjecture144_of_centerDepth_one_girth_ge_five
    (G : SimpleGraph α) (hconn : G.Connected)
    (hq : ecc G G.center = 1) (hg : 5 ≤ G.girth) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have hcyc : ¬G.IsAcyclic := by
    intro hacyc
    have hgZero := hacyc.girth_eq_zero
    omega
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcLength : c.length = G.girth := hgirth.symm
  have hout : ∃ x : α, x ∉ c.support := by
    by_contra hno
    push_neg at hno
    have hzero := hc.centerDepth_eq_zero_of_vertex_cover_wow144
      hcLength hconn hno
    omega
  obtain ⟨x, hxOut⟩ := hout
  have hcycleSet : ((c.support.toFinset : Finset α) : Set α).Nonempty :=
    ⟨z, by simp⟩
  obtain ⟨ku, hku, p, hpPath, hp⟩ :=
    hconn.exists_path_length_eq_distToSet_wow144 x hcycleSet
  have hkuCycle : ku ∈ c.support := by simpa using hku
  have hpPos : 0 < p.length := by
    by_contra hnot
    have hpZero : p.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hxku : x = ku := p.eq_of_length_eq_zero hpZero
    apply hxOut
    simpa [hxku] using hkuCycle
  have hpNotNil : ¬p.Nil := by
    simpa [Walk.not_nil_iff_lt_length] using hpPos
  have hpenAdj : G.Adj p.penultimate ku := p.adj_penultimate hpNotNil
  have hpenOut : p.penultimate ∉ c.support := by
    have hnot := p.getVert_not_mem_of_length_eq_distToSet_wow144 hp
      (i := p.length - 1) (by omega)
    simpa using hnot
  have hpenUnique : ∀ ⦃b : α⦄, b ∈ c.support →
      G.Adj p.penultimate b → b = ku := by
    intro b hb hpb
    exact hc.outside_neighbor_unique_of_length_eq_girth_wow144
      hcLength hg hpenOut hkuCycle hb hpenAdj hpb
  obtain ⟨root, hroot, hrootNe⟩ := hc.exists_support_ne_wow144 hkuCycle
  exact conjecture144_of_centerDepth_one_of_unique_attachment
    G hq hc hroot hcLength hpenOut hkuCycle hrootNe hpenAdj hpenUnique

#print axioms WOW144.conjecture144_of_centerDepth_one_girth_ge_five

end WOW144
