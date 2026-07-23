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

import WOW144.InducedTree

/-!
# Induced geodesic trees

A distance-realizing path is chordless, so its support induces a tree. In a
finite connected graph, a diametral geodesic therefore supplies an induced
tree on `diameter + 1` vertices.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [Fintype α] [Nontrivial α] in
/-- The support of a distance-realizing walk induces a tree. -/
lemma Walk.induce_support_toFinset_isTree_of_length_eq_dist_wow144
    {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset :
          (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext x
        simp
      rw [hset]
      letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
      letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
      exact IsTree.of_subsingleton
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have htree := ih hptail
      have hfullPath := (p.cons huv).isPath_of_length_eq_dist hp
      have huNot : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hfullPath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbSupport : b ∈ (p.cons huv).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa using hb)
        have hedge := (p.cons huv).chordless_of_length_eq_dist hp
          (by simp) hbSupport hub
        simpa using hfullPath.eq_snd_of_mem_edges hedge
      have hsupp : (Walk.cons huv p).support.toFinset =
          insert u p.support.toFinset := by simp
      rw [hsupp]
      exact htree.induce_insert_of_unique_adj_wow144 huNot (by simp) huv huniq

/-- A diametral geodesic supplies an induced tree on `diameter + 1` vertices. -/
lemma diam_add_one_le_largestInducedTreeSize_wow144 (hG : G.Connected) :
    G.diam + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hpPath, hpLength⟩ := hG.exists_path_of_dist u v
  have htree := p.induce_support_toFinset_isTree_of_length_eq_dist_wow144 hpLength
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support]
  calc
    G.diam + 1 = p.length + 1 := by rw [hpLength, huv]
    _ = p.support.toFinset.card := hcard.symm
    _ ≤ largestInducedTreeSize G := finset_card_le_largestInducedTreeSize htree

#print axioms Walk.induce_support_toFinset_isTree_of_length_eq_dist_wow144
#print axioms diam_add_one_le_largestInducedTreeSize_wow144

end SimpleGraph
