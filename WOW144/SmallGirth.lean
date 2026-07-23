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

This module begins the low-girth closure of Conjecture 144. Center depth one
rules out complete graphs and therefore forces diameter at least two. When the
girth is three, a diametral geodesic supplies the required induced tree.
-/

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Center depth one implies that not every vertex is central. -/
lemma center_ne_univ_of_centerDepth_one (G : SimpleGraph α)
    (hq : ecc G G.center = 1) : G.center ≠ Set.univ := by
  intro hcenter
  rw [hcenter] at hq
  simp [ecc] at hq

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

#print axioms WOW144.conjecture144_of_centerDepth_one_girth_three

end WOW144
