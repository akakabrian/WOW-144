import WOW144.Geodesic

/-!
# Neighbor indices on a geodesic

A two-edge shortcut through one vertex forces any two of its neighbors on a
geodesic to occur within two indices. At girth at least four, two distinct such
neighbors are exactly two indices apart.
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

omit [Fintype α] [DecidableEq α] in
lemma Walk.IsPath.concat_two_isCycle_neighbor_wow144
    {a b x : α} {p : G.Walk a b} (hp : p.IsPath) (hab : a ≠ b)
    (hx : x ∉ p.support) (hbx : G.Adj b x) (hxa : G.Adj x a) :
    ((p.concat hbx).concat hxa).IsCycle := by
  have hpx : (p.concat hbx).IsPath := hp.concat hx hbx
  rw [← Walk.isCycle_reverse, Walk.reverse_concat, Walk.cons_isCycle_iff]
  refine ⟨(Walk.isPath_reverse_iff _).2 hpx, ?_⟩
  intro he
  have he' : s(x, a) ∈ (p.concat hbx).edges := by
    have he0 : s(a, x) ∈ (p.concat hbx).edges := by
      simpa only [Walk.edges_reverse, List.mem_reverse] using he
    rw [Sym2.eq_swap]
    exact he0
  have ha : a = (p.concat hbx).penultimate := hpx.eq_penultimate_of_mem_edges he'
  exact hab (by simpa using ha)

omit [Fintype α] [DecidableEq α] in
/-- At girth at least four, two distinct neighbors of one outside vertex on a
geodesic are the endpoints of a two-edge path segment. -/
lemma Walk.geodesic_distinct_neighbor_indices_gap_two_wow144
    {u v x : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hxOut : x ∉ p.support)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j))
    (hij : i ≠ j) (hg : 4 ≤ G.girth) :
    i + 2 = j ∨ j + 2 = i := by
  have hgap := p.geodesic_neighbor_indices_within_two_wow144 hp hi hj hxi hxj
  have noConsecutive : ∀ {a : ℕ}, a + 1 ≤ p.length →
      G.Adj x (p.getVert a) → G.Adj x (p.getVert (a + 1)) → False := by
    intro a ha hxa hxb
    have hab : G.Adj (p.getVert a) (p.getVert (a + 1)) :=
      p.adj_getVert_succ (by omega)
    have hxEdgeOut : x ∉ hab.toWalk.support := by
      simp only [SimpleGraph.Adj.toWalk, Walk.support_cons, Walk.support_nil,
        List.mem_cons, not_or]
      refine ⟨?_, ?_, by simp⟩
      · intro h
        apply hxOut
        rw [h]
        exact p.getVert_mem_support a
      · intro h
        apply hxOut
        rw [h]
        exact p.getVert_mem_support (a + 1)
    have habPath : hab.toWalk.IsPath := by
      apply Walk.IsPath.mk'
      simp [hab.ne]
    have hcycle := habPath.concat_two_isCycle_neighbor_wow144
      hab.ne hxEdgeOut hxb.symm hxa
    have hshort := G.girth_le_length hcycle
    norm_num at hshort
    omega
  rcases lt_or_gt_of_ne hij with hij | hji
  · left
    by_cases hsucc : j = i + 1
    · exact (noConsecutive (a := i) (by omega) hxi (by simpa [hsucc] using hxj)).elim
    · omega
  · right
    by_cases hsucc : i = j + 1
    · exact (noConsecutive (a := j) (by omega) hxj (by simpa [hsucc] using hxi)).elim
    · omega

#print axioms Walk.geodesic_neighbor_indices_within_two_wow144
#print axioms Walk.geodesic_distinct_neighbor_indices_gap_two_wow144

end SimpleGraph
