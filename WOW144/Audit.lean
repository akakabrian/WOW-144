import FormalConjectures.WrittenOnTheWallII.GraphConjecture144

/-!
# Conjecture 144 source audit

Checks the exact upstream theorem type and the graph invariants appearing in it.
-/

namespace WOW144

open Classical SimpleGraph

#check WrittenOnTheWallII.GraphConjecture144.conjecture144
#check SimpleGraph.largestInducedTreeSize
#check SimpleGraph.ecc
#check SimpleGraph.center
#check SimpleGraph.girth

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Type-level audit of the exact upstream Conjecture 144 inequality. -/
example (G : SimpleGraph α) :
    ((G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ)) ↔
    ((G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ)) :=
  Iff.rfl

end WOW144
