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
import WOW144.Geodesic

/-!
# Extending an induced geodesic by one vertex

A distance-realizing path induces a tree. If a vertex outside that path has
exactly one neighbor on it, adjoining the vertex preserves the induced-tree
property and increases the order by one. Applied to a diametral geodesic, this
gives an induced tree on `diameter + 2` vertices.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [Fintype α] [Nontrivial α] in
/-- A distance-realizing path with one uniquely attached outside vertex yields
an induced tree with two more vertices than the path length. -/
lemma Walk.unique_outside_attachment_length_add_two_le_tree_wow144
    {u v x a : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v)
    (hxOut : x ∉ p.support) (ha : a ∈ p.support)
    (hxa : G.Adj x a)
    (huniq : ∀ ⦃b : α⦄, b ∈ p.support → G.Adj x b → b = a) :
    p.length + 2 ≤ largestInducedTreeSize G := by
  have hpPath : p.IsPath := p.isPath_of_length_eq_dist hp
  have htree := p.induce_support_toFinset_isTree_of_length_eq_dist_wow144 hp
  have hxFin : x ∉ p.support.toFinset := by simpa using hxOut
  have haFin : a ∈ p.support.toFinset := by simpa using ha
  have huniqFin : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj x b → b = a := by
    intro b hb hxb
    exact huniq (by simpa using hb) hxb
  have htree' :
      (G.induce ((insert x p.support.toFinset : Finset α) : Set α)).IsTree :=
    htree.induce_insert_of_unique_adj_wow144 hxFin haFin hxa huniqFin
  have hsupportCard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support]
  have hcard : (insert x p.support.toFinset).card = p.length + 2 := by
    rw [Finset.card_insert_of_notMem hxFin, hsupportCard]
    omega
  calc
    p.length + 2 = (insert x p.support.toFinset).card := hcard.symm
    _ ≤ largestInducedTreeSize G :=
      finset_card_le_largestInducedTreeSize htree'

omit [Fintype α] [Nontrivial α] in
/-- A uniquely extendable diametral geodesic gives an induced tree on
`diameter + 2` vertices. -/
lemma Walk.unique_outside_attachment_diam_add_two_le_tree_wow144
    {u v x a : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hdiam : G.dist u v = G.diam)
    (hxOut : x ∉ p.support) (ha : a ∈ p.support)
    (hxa : G.Adj x a)
    (huniq : ∀ ⦃b : α⦄, b ∈ p.support → G.Adj x b → b = a) :
    G.diam + 2 ≤ largestInducedTreeSize G := by
  have hbound := p.unique_outside_attachment_length_add_two_le_tree_wow144
    hp hxOut ha hxa huniq
  omega

#print axioms Walk.unique_outside_attachment_length_add_two_le_tree_wow144
#print axioms Walk.unique_outside_attachment_diam_add_two_le_tree_wow144

end SimpleGraph
