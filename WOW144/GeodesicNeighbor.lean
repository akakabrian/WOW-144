import WOW144.Geodesic

/-!
# Neighbor indices on a geodesic

A two-edge shortcut through one vertex forces any two of its neighbors on a
geodesic to occur within two indices.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [Fintype α] [DecidableEq α] in
lemma Walk.geodesic_neighbor_indices_within_two_wow144
    {u v x : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j)) :
    i ≤ j + 2 ∧ j ≤ i + 2 := by
  have key : ∀ {a b : ℕ}, a ≤ p.length → b ≤ p.length → a ≤ b →
      G.Adj x (p.getVert a) → G.Adj x (p.getVert b) → b ≤ a + 2 := by
    intro a b ha hb hab hxa hxb
    let shortcut : G.Walk u v :=
      (((p.take a).concat hxa.symm).concat hxb).append (p.drop b)
    have hdist := G.dist_le shortcut
    have hlength : shortcut.length = a + 2 + (p.length - b) := by
      dsimp [shortcut]
      rw [Walk.length_append, Walk.length_concat, Walk.length_concat,
        Walk.take_length, Walk.drop_length, Nat.min_eq_left ha]
      omega
    rw [← hp, hlength] at hdist
    omega
  constructor
  · by_cases hij : i ≤ j
    · omega
    · exact key hj hi (Nat.le_of_not_ge hij) hxj hxi
  · by_cases hij : i ≤ j
    · exact key hi hj hij hxi hxj
    · omega

#print axioms Walk.geodesic_neighbor_indices_within_two_wow144

end SimpleGraph
