import WOW144.NearestCycle

/-!
# Depth along a nearest-set path

Along a walk whose length realizes the distance to a nonempty target set, the
vertex at index `i` has target-set distance exactly the number of remaining
edges.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [DecidableEq α] in
lemma Walk.distToSet_getVert_eq_length_sub_of_nearest_wow144
    {S : Set α} {u v : α} (hconn : G.Connected) (p : G.Walk u v)
    (hv : v ∈ S) (hp : p.length = G.distToSet u S)
    {i : ℕ} (hi : i ≤ p.length) :
    G.distToSet (p.getVert i) S = p.length - i := by
  have hupperSet := distToSet_le_dist_of_mem_wow144 (G := G) (p.getVert i) hv
  have hupperDist : G.dist (p.getVert i) v ≤ (p.drop i).length :=
    G.dist_le (p.drop i)
  have hupper : G.distToSet (p.getVert i) S ≤ p.length - i := by
    rw [Walk.drop_length] at hupperDist
    omega
  obtain ⟨s, hsS, hsEq⟩ :=
    exists_mem_dist_eq_distToSet_wow144 (G := G) (p.getVert i) ⟨v, hv⟩
  obtain ⟨r, hr⟩ := hconn.exists_walk_length_eq_dist (p.getVert i) s
  let w : G.Walk u s := (p.take i).append r
  have hbase := distToSet_le_dist_of_mem_wow144 (G := G) u hsS
  have hdistWalk : G.dist u s ≤ w.length := G.dist_le w
  have htake : (p.take i).length = i := by
    rw [Walk.take_length, Nat.min_eq_left hi]
  have hwlen : w.length = i + G.distToSet (p.getVert i) S := by
    simp only [w, Walk.length_append, htake, hr, hsEq]
  have hlower : p.length ≤ w.length := by
    calc
      p.length = G.distToSet u S := hp
      _ ≤ G.dist u s := hbase
      _ ≤ w.length := hdistWalk
  rw [hwlen] at hlower
  omega

#print axioms Walk.distToSet_getVert_eq_length_sub_of_nearest_wow144

end SimpleGraph
