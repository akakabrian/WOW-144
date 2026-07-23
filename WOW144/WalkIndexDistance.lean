import WOW144.Geodesic

/-!
# Distance between indexed vertices of a walk

The segment of a walk between indices `i ≤ j` has length `j - i`, so it gives
a direct upper bound on graph distance between those indexed vertices.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [Fintype α] [DecidableEq α] in
lemma Walk.dist_getVert_le_sub_wow144
    {u v : α} (p : G.Walk u v)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) ≤ j - i := by
  have hdist := G.dist_le ((p.drop i).take (j - i))
  simpa [Walk.drop_getVert, Nat.add_sub_of_le hij,
    Walk.take_length, Walk.drop_length,
    Nat.min_eq_left (by omega : j - i ≤ p.length - i)] using hdist

#print axioms Walk.dist_getVert_le_sub_wow144

end SimpleGraph
