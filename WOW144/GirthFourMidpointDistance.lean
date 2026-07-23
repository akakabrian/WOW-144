import WOW144.WalkIndexDistance

/-!
# Midpoint distance in a dominating girth-four path structure

Suppose every vertex is either on a path or is adjacent to the endpoints of a
two-edge segment of that path. When the path has length at least three, every
vertex is within `length - length / 2` of the midpoint vertex.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [Fintype α] [DecidableEq α] in
lemma Walk.dominating_four_corner_midpoint_distance_le_wow144
    {u v : α} (p : G.Walk u v) (hconn : G.Connected)
    (hthree : 3 ≤ p.length)
    (hstructure : ∀ x : α,
      x ∈ p.support ∨
        ∃ i : ℕ, i + 2 ≤ p.length ∧
          G.Adj x (p.getVert i) ∧ G.Adj x (p.getVert (i + 2))) :
    ∀ x : α,
      G.dist x (p.getVert (p.length / 2)) ≤ p.length - p.length / 2 := by
  intro x
  rcases hstructure x with hxPath | ⟨i, hiTwo, hxi, hxiTwo⟩
  · obtain ⟨j, hjEq, hjLe⟩ :=
      Walk.mem_support_iff_exists_getVert.mp hxPath
    have hmLe : p.length / 2 ≤ p.length := Nat.div_le_self _ _
    rcases le_total j (p.length / 2) with hjm | hmj
    · have hd := p.dist_getVert_le_sub_wow144 hjm hmLe
      have hd' : G.dist x (p.getVert (p.length / 2)) ≤ p.length / 2 - j := by
        simpa [hjEq] using hd
      omega
    · have hd := p.dist_getVert_le_sub_wow144 hmj hjLe
      have hd' : G.dist x (p.getVert (p.length / 2)) ≤ j - p.length / 2 := by
        simpa [G.dist_comm, hjEq] using hd
      omega
  · have hiLe : i ≤ p.length := by omega
    have hiTwoLe : i + 2 ≤ p.length := hiTwo
    have hxiDist : G.dist x (p.getVert i) = 1 :=
      dist_eq_one_iff_adj.mpr hxi
    have hxiTwoDist : G.dist x (p.getVert (i + 2)) = 1 :=
      dist_eq_one_iff_adj.mpr hxiTwo
    by_cases hmLeft : p.length / 2 ≤ i
    · have hpath := p.dist_getVert_le_sub_wow144 hmLeft hiLe
      have hpath' :
          G.dist (p.getVert i) (p.getVert (p.length / 2)) ≤
            i - p.length / 2 := by
        simpa only [G.dist_comm] using hpath
      have htri := hconn.dist_triangle
        (u := x) (v := p.getVert i) (w := p.getVert (p.length / 2))
      omega
    · by_cases hright : i + 2 ≤ p.length / 2
      · have hpath := p.dist_getVert_le_sub_wow144 hright
          (Nat.div_le_self p.length 2)
        have htri := hconn.dist_triangle
          (u := x) (v := p.getVert (i + 2))
          (w := p.getVert (p.length / 2))
        omega
      · have himid : i < p.length / 2 := Nat.lt_of_not_ge hmLeft
        have hmidTwo : p.length / 2 < i + 2 := Nat.lt_of_not_ge hright
        have hmidEq : p.length / 2 = i + 1 := by omega
        have hpath := p.dist_getVert_le_sub_wow144
          (show i ≤ p.length / 2 by omega)
          (Nat.div_le_self p.length 2)
        have htri := hconn.dist_triangle
          (u := x) (v := p.getVert i) (w := p.getVert (p.length / 2))
        omega

#print axioms Walk.dominating_four_corner_midpoint_distance_le_wow144

end SimpleGraph
