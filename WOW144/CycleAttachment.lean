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

/-!
# Unique attachments to a shortest cycle

A vertex with exactly one neighbor on a girth-realizing cycle can be attached
to the cycle after deleting a different cycle vertex. The result is an induced
tree on exactly `girth` vertices.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

/-- A unique outside attachment to a shortest cycle supplies an induced tree on
exactly `girth` vertices. -/
lemma Walk.IsCycle.unique_attachment_girth_le_largestInducedTreeSize_wow144
    {v root y a : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hroot : root ∈ c.support) (hcLength : c.length = G.girth)
    (hyOut : y ∉ c.support) (haCycle : a ∈ c.support)
    (hrootNeA : root ≠ a) (hya : G.Adj y a)
    (huniq : ∀ ⦃b : α⦄, b ∈ c.support → G.Adj y b → b = a) :
    G.girth ≤ largestInducedTreeSize G := by
  let r := c.rotate hroot
  let base := r.tail.dropLast
  have hcert :
      base.IsPath ∧
        base.support.toFinset = c.support.toFinset.erase root ∧
        (G.induce (base.support.toFinset : Set α)).IsTree ∧
        base.support.toFinset.card = c.length - 1 := by
    simpa only [r, base] using
      hc.erase_vertex_path_certificate_wow144 hroot hcLength
  rcases hcert with ⟨_, hbaseSupport, hbaseTree, hbaseCard⟩
  have hyNotBase : y ∉ base.support.toFinset := by
    intro hyBase
    apply hyOut
    have hyErase : y ∈ c.support.toFinset.erase root := by
      simpa only [hbaseSupport] using hyBase
    simpa using Finset.mem_of_mem_erase hyErase
  have haBase : a ∈ base.support.toFinset := by
    rw [hbaseSupport]
    exact Finset.mem_erase.mpr ⟨hrootNeA.symm, by simpa using haCycle⟩
  have huniqBase : ∀ ⦃b : α⦄, b ∈ base.support.toFinset → G.Adj y b → b = a := by
    intro b hb hAdj
    apply huniq
    · rw [hbaseSupport] at hb
      simpa using Finset.mem_of_mem_erase hb
    · exact hAdj
  have htree :
      (G.induce ((insert y base.support.toFinset : Finset α) : Set α)).IsTree :=
    hbaseTree.induce_insert_of_unique_adj_wow144 hyNotBase haBase hya huniqBase
  have hcard : (insert y base.support.toFinset).card = c.length := by
    rw [Finset.card_insert_of_notMem hyNotBase, hbaseCard]
    have hthree : 3 ≤ c.length := hc.three_le_length
    omega
  calc
    G.girth = c.length := hcLength.symm
    _ = (insert y base.support.toFinset).card := hcard.symm
    _ ≤ largestInducedTreeSize G := finset_card_le_largestInducedTreeSize htree

#print axioms Walk.IsCycle.unique_attachment_girth_le_largestInducedTreeSize_wow144

end SimpleGraph

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The exact Conjecture 144 inequality follows at center depth one from a
certified unique attachment to a shortest cycle. -/
theorem conjecture144_of_centerDepth_one_of_unique_attachment
    (G : SimpleGraph α) (hq : ecc G G.center = 1)
    {v root y a : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hroot : root ∈ c.support) (hcLength : c.length = G.girth)
    (hyOut : y ∉ c.support) (haCycle : a ∈ c.support)
    (hrootNeA : root ≠ a) (hya : G.Adj y a)
    (huniq : ∀ ⦃b : α⦄, b ∈ c.support → G.Adj y b → b = a) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have htree := hc.unique_attachment_girth_le_largestInducedTreeSize_wow144
    hroot hcLength hyOut haCycle hrootNeA hya huniq
  apply conjecture144_of_nat_bound G
  rw [hq]
  omega

#print axioms WOW144.conjecture144_of_centerDepth_one_of_unique_attachment

end WOW144
