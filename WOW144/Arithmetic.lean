import FormalConjectures.WrittenOnTheWallII.GraphConjecture144

/-!
# Arithmetic reduction for Conjecture 144

Reduces the exact real-valued statement to an integral inequality.
-/

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α]

/-- It suffices to prove the target inequality in the equivalent natural-number form
`girth + centerDepth ≤ largestInducedTreeSize + 1`. -/
theorem conjecture144_of_nat_bound (G : SimpleGraph α)
    (h : G.girth + ecc G G.center ≤ largestInducedTreeSize G + 1) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have hr :
      (G.girth : ℝ) + (ecc G G.center : ℝ) ≤
        (largestInducedTreeSize G : ℝ) + 1 := by
    exact_mod_cast h
  linarith

end WOW144
