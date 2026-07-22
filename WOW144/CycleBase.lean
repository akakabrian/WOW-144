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

import WOW144.Arithmetic
import WOW144.InducedTree

/-!
# Shortest-cycle induced-tree base for Conjecture 144

This module isolates the shortest-cycle construction used in the checked
Conjecture 142 development. Deleting one vertex from a girth-realizing cycle
leaves an induced tree on exactly `girth - 1` vertices. The lemmas are locally
renamed and reproduced under the upstream Apache-2.0 license rather than
changing the authoritative Formal Conjectures dependency.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [Fintype α] in
/-- Attaching a new vertex along its unique neighbor in an induced tree gives a larger
induced tree. -/
lemma IsTree.induce_insert_of_unique_adj_wow144 {s : Finset α} {z a : α}
    (hT : (G.induce (s : Set α)).IsTree)
    (_hz : z ∉ s) (ha : a ∈ s) (hza : G.Adj z a)
    (huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a) :
    (G.induce ((insert z s : Finset α) : Set α)).IsTree := by
  classical
  constructor
  · have hsconn : (G.induce (s : Set α)).Preconnected := hT.isConnected.preconnected
    have hzconn : (G.induce ({z} : Set α)).Preconnected := .of_subsingleton
    have hconn := connected_induce_union (v := z) (w := a) (s := ({z} : Set α))
      (t := (s : Set α)) hzconn hsconn (by simp) (by simpa using ha) hza
    rw [Finset.coe_insert]
    simpa only [Set.singleton_union] using hconn
  · intro v c hc
    let e : G.induce ((insert z s : Finset α) : Set α) ↪g G :=
      SimpleGraph.Embedding.induce _
    let q : G.Walk (e v) (e v) := c.map e.toHom
    have hq : q.IsCycle := by
      dsimp [q]
      exact (Walk.map_isCycle_iff_of_injective e.injective).2 hc
    have hq_mem (w : α) (hw : w ∈ q.support) : w ∈ insert z s := by
      dsimp [q] at hw
      rw [Walk.support_map] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      change (w' : α) ∈ insert z s
      exact w'.property
    by_cases hzq : z ∈ q.support
    · let r : G.Walk z z := q.rotate hzq
      have hr : r.IsCycle := by
        dsimp [r]
        exact hq.rotate hzq
      have hrsnd : r.snd ∈ q.support := by
        apply (q.mem_support_rotate_iff hzq).mp
        simpa only [r] using r.getVert_mem_support 1
      have hrpenultimate : r.penultimate ∈ q.support := by
        apply (q.mem_support_rotate_iff hzq).mp
        simpa only [r] using r.getVert_mem_support (r.length - 1)
      have hadj_snd : G.Adj z r.snd := r.adj_snd hr.not_nil
      have hadj_penultimate : G.Adj z r.penultimate :=
        (r.adj_penultimate hr.not_nil).symm
      have hsnd : r.snd ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrsnd) with heq | hmem
        · exact (hadj_snd.ne heq.symm).elim
        · exact hmem
      have hpenultimate : r.penultimate ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrpenultimate) with heq | hmem
        · exact (hadj_penultimate.ne heq.symm).elim
        · exact hmem
      exact hr.snd_ne_penultimate <|
        (huniq hsnd hadj_snd).trans (huniq hpenultimate hadj_penultimate).symm
    · have hqs : ∀ w ∈ q.support, w ∈ (s : Set α) := by
        intro w hw
        rcases Finset.mem_insert.mp (hq_mem w hw) with heq | hmem
        · subst w
          exact (hzq hw).elim
        · simpa using hmem
      let qi := q.induce (s : Set α) hqs
      have hqi : qi.IsCycle := by
        apply (Walk.map_isCycle_iff_of_injective
          (f := (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom)
          (SimpleGraph.Embedding.induce (G := G) (s : Set α)).injective).mp
        rw [show qi.map (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom = q by
          dsimp [qi]
          exact Walk.map_induce q hqs]
        exact hq
      exact hT.IsAcyclic qi hqi

omit [Fintype α] [DecidableEq α] in
/-- Every path with fewer vertices than the girth is chordless in the ambient graph. -/
lemma Walk.chordless_of_length_succ_lt_girth_wow144
    {u v : α} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length + 1 < G.girth) :
    ∀ ⦃x y : α⦄, x ∈ p.support → y ∈ p.support →
      G.Adj x y → s(x, y) ∈ p.edges := by
  intro x y hx hy hxy
  by_contra hnot
  obtain ⟨i, hiEq, hiLe⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  obtain ⟨j, hjEq, hjLe⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  have hijNe : i ≠ j := by
    intro hij
    apply hxy.ne
    calc
      x = p.getVert i := hiEq.symm
      _ = p.getVert j := by rw [hij]
      _ = y := hjEq
  have key : ∀ {i j : ℕ} {x y : α},
      p.getVert i = x → i ≤ p.length → p.getVert j = y → j ≤ p.length →
      i < j → G.Adj x y → s(x, y) ∉ p.edges → False := by
    intro i j x y hiEq hiLe hjEq hjLe hij hxy hnot
    let seg0 := (p.drop i).take (j - i)
    have hsub : seg0.IsSubwalk p := by
      exact (Walk.isSubwalk_take (p.drop i) (j - i)).trans
        (Walk.isSubwalk_drop p i)
    have hend : (p.drop i).getVert (j - i) = y := by
      rw [Walk.drop_getVert, Nat.add_sub_of_le (Nat.le_of_lt hij), hjEq]
    let seg : G.Walk x y := seg0.copy hiEq hend
    have hsegPath : seg.IsPath := by
      dsimp [seg]
      simpa using isPath_of_isSubwalk hsub hp
    have hnotSeg : s(y, x) ∉ seg.edges := by
      intro he
      apply hnot
      have he0 : s(y, x) ∈ seg0.edges := by simpa [seg] using he
      have hep : s(y, x) ∈ p.edges := hsub.edges_subset he0
      simpa only [Sym2.eq_swap] using hep
    have hcyc : (Walk.cons hxy.symm seg).IsCycle := by
      rw [Walk.cons_isCycle_iff]
      exact ⟨hsegPath, hnotSeg⟩
    have hgLe := G.girth_le_length hcyc
    have hsegLe : seg.length ≤ p.length := by
      simpa [seg] using Walk.length_le_of_isSubwalk hsub
    simp only [Walk.length_cons] at hgLe
    omega
  rcases lt_or_gt_of_ne hijNe with hij | hji
  · exact key hiEq hiLe hjEq hjLe hij hxy hnot
  · have hnotYX : s(y, x) ∉ p.edges := by
      simpa only [Sym2.eq_swap] using hnot
    exact key hjEq hjLe hiEq hiLe hji hxy.symm hnotYX

omit [Fintype α] in
/-- A path shorter than the girth by at least one vertex induces a tree. -/
lemma Walk.induce_support_isTree_of_isPath_of_length_succ_lt_girth_wow144
    {u v : α} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length + 1 < G.girth) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset : (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext
        simp
      rw [hset]
      letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
      letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
      exact IsTree.of_subsingleton
  | @cons u v w huv p ih =>
      have hfull : (p.cons huv).IsPath := hp
      rw [Walk.cons_isPath_iff] at hp
      have htailShort : p.length + 1 < G.girth := by
        rw [Walk.length_cons] at hlen
        omega
      have htree := ih hp.1 htailShort
      have huNot : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hfull.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbmem : b ∈ p.support := by simpa using hb
        have hedge := (p.cons huv).chordless_of_length_succ_lt_girth_wow144
          hfull hlen (by simp) (by simp [hbmem]) hub
        simpa using hfull.eq_snd_of_mem_edges hedge
      have hsupp : (Walk.cons huv p).support.toFinset =
          insert u p.support.toFinset := by simp
      rw [hsupp]
      exact htree.induce_insert_of_unique_adj_wow144 huNot (by simp) huv huniq

omit [Fintype α] in
/-- Rotation preserves the length of a closed walk. -/
lemma Walk.length_rotate_wow144 {u v : α} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).length = c.length := by
  calc
    (c.rotate h).length = (c.rotate h).edges.length := (Walk.length_edges _).symm
    _ = c.edges.length := (c.rotate_edges h).perm.length_eq
    _ = c.length := Walk.length_edges c

omit [Fintype α] in
/-- Deleting a chosen vertex from a girth-realizing cycle leaves an induced path
on exactly `girth - 1` vertices. -/
lemma Walk.IsCycle.erase_vertex_path_certificate_wow144
    {v root : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hroot : root ∈ c.support) (hcLength : c.length = G.girth) :
    let r := c.rotate hroot
    let base := r.tail.dropLast
    base.IsPath ∧
      base.support.toFinset = c.support.toFinset.erase root ∧
      (G.induce (base.support.toFinset : Set α)).IsTree ∧
      base.support.toFinset.card = c.length - 1 := by
  let r := c.rotate hroot
  let base := r.tail.dropLast
  have hrCycle : r.IsCycle := by
    dsimp [r]
    exact hc.rotate hroot
  have hrLen : r.length = c.length := by
    dsimp [r]
    exact c.length_rotate_wow144 hroot
  have hrNotNil : ¬r.Nil := hrCycle.not_nil
  have hrThree : 3 ≤ r.length := hrCycle.three_le_length
  have htailLen : r.tail.length + 1 = r.length :=
    r.length_tail_add_one hrNotNil
  have htailPos : 0 < r.tail.length := by omega
  have hbaseSupp : base.support = r.tail.support.dropLast := by
    dsimp [base]
    rw [Walk.dropLast, Walk.take_support_eq_support_take_succ,
      List.dropLast_eq_take, r.tail.length_support]
    congr 1
    omega
  have htailSupp : r.tail.support = r.support.tail :=
    r.support_tail_of_not_nil hrNotNil
  have hbasePath : base.IsPath := by
    apply Walk.IsPath.mk'
    rw [hbaseSupp, htailSupp, List.dropLast_eq_take]
    exact hrCycle.support_nodup.take
  have hbaseLen : base.length = r.length - 2 := by
    dsimp [base]
    rw [Walk.dropLast, Walk.take_length]
    omega
  have hbaseShort : base.length + 1 < G.girth := by
    rw [hbaseLen, hrLen, hcLength]
    omega
  have hbaseTree :=
    base.induce_support_isTree_of_isPath_of_length_succ_lt_girth_wow144
      hbasePath hbaseShort
  have hsupportEq :
      base.support.toFinset = c.support.toFinset.erase root := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_erase]
    constructor
    · intro hx
      have hxDrop : x ∈ r.tail.support.dropLast := by
        rw [← hbaseSupp]
        exact hx
      have hxTail : x ∈ r.tail.support := List.dropLast_subset _ hxDrop
      have hxRTail : x ∈ r.support.tail := by simpa [htailSupp] using hxTail
      have hxR : x ∈ r.support := List.mem_of_mem_tail hxRTail
      have hxCycle : x ∈ c.support :=
        (c.mem_support_rotate_iff hroot).mp hxR
      have htailNodup : r.tail.support.Nodup := by
        rw [htailSupp]
        exact hrCycle.support_nodup
      have hxNe : x ≠ root := by
        have hrel := htailNodup.rel_dropLast_getLast hxDrop
        simpa using hrel
      exact ⟨hxNe, hxCycle⟩
    · rintro ⟨hxNe, hxCycle⟩
      have hxR : x ∈ r.support :=
        (c.mem_support_rotate_iff hroot).mpr hxCycle
      have hxRTail : x ∈ r.support.tail := by
        rw [r.support_eq_cons] at hxR
        rcases List.mem_cons.mp hxR with hxRoot | hxTail
        · exact (hxNe hxRoot).elim
        · exact hxTail
      have hxTail : x ∈ r.tail.support := by
        rw [htailSupp]
        exact hxRTail
      have hxLast : x ≠ r.tail.support.getLast r.tail.support_ne_nil := by
        simpa using hxNe
      have hxDrop : x ∈ r.tail.support.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast hxTail hxLast
      rw [hbaseSupp]
      exact hxDrop
  have hbaseCard : base.support.toFinset.card = c.length - 1 := by
    rw [List.toFinset_card_of_nodup hbasePath.support_nodup,
      base.length_support, hbaseLen, hrLen]
    omega
  exact ⟨hbasePath, hsupportEq, hbaseTree, hbaseCard⟩

/-- Every cyclic graph contains an induced tree on at least `girth - 1` vertices. -/
theorem girth_sub_one_le_largestInducedTreeSize_wow144
    (G : SimpleGraph α) (hcyc : ¬G.IsAcyclic) :
    G.girth - 1 ≤ largestInducedTreeSize G := by
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  let r := c.rotate (by simp : z ∈ c.support)
  let base := r.tail.dropLast
  have hcert := hc.erase_vertex_path_certificate_wow144
    (by simp : z ∈ c.support) hgirth.symm
  change base.IsPath ∧
      base.support.toFinset = c.support.toFinset.erase z ∧
      (G.induce (base.support.toFinset : Set α)).IsTree ∧
      base.support.toFinset.card = c.length - 1 at hcert
  rcases hcert with ⟨_, _, htree, hcard⟩
  calc
    G.girth - 1 = c.length - 1 := by rw [hgirth]
    _ = base.support.toFinset.card := hcard.symm
    _ ≤ largestInducedTreeSize G := finset_card_le_largestInducedTreeSize htree

end SimpleGraph

namespace WOW144

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Conjecture 144 holds whenever the eccentricity of the center set is zero. -/
theorem conjecture144_of_centerDepth_zero (G : SimpleGraph α)
    (hq : ecc G G.center = 0) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have hnat : G.girth + ecc G G.center ≤ largestInducedTreeSize G + 1 := by
    rw [hq, Nat.add_zero]
    by_cases hcyc : G.IsAcyclic
    · rw [hcyc.girth_eq_zero]
      omega
    · have hbase := girth_sub_one_le_largestInducedTreeSize_wow144 G hcyc
      omega
  exact conjecture144_of_nat_bound G hnat

#print axioms SimpleGraph.girth_sub_one_le_largestInducedTreeSize_wow144
#print axioms WOW144.conjecture144_of_centerDepth_zero

end WOW144
