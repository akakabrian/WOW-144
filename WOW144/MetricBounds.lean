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
# Metric bounds for Conjecture 144

The eccentricity of the center set is bounded by the graph diameter. Together
with the induced diametral-geodesic tree, this proves the exact Conjecture 144
statement for every connected acyclic graph.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [DecidableEq α] in
/-- The maximum distance from a noncenter vertex to the center is at most the
diameter. -/
lemma centerDepth_le_diam_wow144 (hconn : G.Connected) :
    ecc G G.center ≤ G.diam := by
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  unfold ecc
  dsimp only
  split_ifs with hout
  · apply Finset.max'_le
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨v, -, rfl⟩
    obtain ⟨c, hc⟩ := G.center_nonempty
    exact (distToSet_le_dist_of_mem_wow144 (G := G) v hc).trans
      (dist_le_diam hfinite)
  · exact Nat.zero_le _

#print axioms centerDepth_le_diam_wow144

end SimpleGraph

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Conjecture 144 holds for every connected acyclic graph. -/
theorem conjecture144_of_acyclic
    (G : SimpleGraph α) (hconn : G.Connected) (hacyc : G.IsAcyclic) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have hqD := centerDepth_le_diam_wow144 (G := G) hconn
  have htree := diam_add_one_le_largestInducedTreeSize_wow144 (G := G) hconn
  apply conjecture144_of_nat_bound G
  rw [hacyc.girth_eq_zero]
  omega

#print axioms WOW144.conjecture144_of_acyclic

end WOW144
