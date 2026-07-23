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

import WOW144.SmallGirth

/-!
# Complete center-depth-at-most-one case

This module assembles the acyclic case and the girth-three, girth-four, and
girth-at-least-five cyclic cases into exact Conjecture 144 theorems for center
depth one and, consequently, center depth at most one.
-/

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Conjecture 144 holds whenever the center depth is exactly one. -/
theorem conjecture144_of_centerDepth_one
    (G : SimpleGraph α) (hconn : G.Connected)
    (hq : ecc G G.center = 1) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  by_cases hacyc : G.IsAcyclic
  · apply conjecture144_of_nat_bound G
    rw [hq, hacyc.girth_eq_zero]
    omega
  have hg3 : 3 ≤ G.girth := three_le_girth hacyc
  by_cases hthree : G.girth = 3
  · exact conjecture144_of_centerDepth_one_girth_three G hconn hq hthree
  by_cases hfour : G.girth = 4
  · exact conjecture144_of_centerDepth_one_girth_four G hconn hq hfour
  have hg5 : 5 ≤ G.girth := by omega
  exact conjecture144_of_centerDepth_one_girth_ge_five G hconn hq hg5

/-- Conjecture 144 holds whenever the center depth is at most one. -/
theorem conjecture144_of_centerDepth_le_one
    (G : SimpleGraph α) (hconn : G.Connected)
    (hq : ecc G G.center ≤ 1) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  by_cases hzero : ecc G G.center = 0
  · exact conjecture144_of_centerDepth_zero G hzero
  have hone : ecc G G.center = 1 := by omega
  exact conjecture144_of_centerDepth_one G hconn hone

#print axioms WOW144.conjecture144_of_centerDepth_one
#print axioms WOW144.conjecture144_of_centerDepth_le_one

end WOW144
