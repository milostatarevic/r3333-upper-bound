import Ramsey61.Uniform
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Sort

namespace Ramsey61
open Finset SimpleGraph

namespace DenseBipartite

variable {V : Type*} {G : SimpleGraph V}

/-- The parity-coloring direction of Mathlib's
`two_colorable_iff_forall_loop_even`, adapted from
`Mathlib/Combinatorics/SimpleGraph/Coloring/Constructions.lean` at the pinned
revision. That source is copyright 2023 Ivan Renison, Apache 2.0. Keeping
this short checked direction here avoids importing unrelated concrete graph
coloring constructions. -/
theorem colorable_two_of_closed_walk_even
    (h : ∀ u, ∀ p : G.Walk u u, Even p.length) : G.Colorable 2 := by
  classical
  simp_rw [← Nat.not_odd_iff_even] at h
  apply SimpleGraph.colorable_iff_forall_connectedComponents.2
  intro c
  obtain ⟨_, hv⟩ := c.nonempty_supp
  use fun a => Fin.ofNat 2 (c.connected_toSimpleGraph ⟨_, hv⟩ a).some.length
  intro a b hab he
  apply h _ <| (((c.connected_toSimpleGraph ⟨_, hv⟩ a).some.concat hab).append
    (c.connected_toSimpleGraph ⟨_, hv⟩ b).some.reverse).map c.toSimpleGraph_hom
  rw [Walk.length_map, Walk.length_append, Walk.length_concat, Walk.length_reverse,
    add_right_comm]
  have hp : ((Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ a)).length) % 2 =
      (Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ b)).length % 2 := by
    simp_rw [← Fin.val_natCast, ← Fin.ofNat_eq_cast, he]
  exact (Nat.even_iff.mpr (by omega)).add_one

/-- A shortest odd closed walk suffices; no cycle enumeration is needed. -/
theorem exists_shortest_odd_closed_walk (h : ¬G.Colorable 2) :
    ∃ u, ∃ p : G.Walk u u, Odd p.length ∧
      ∀ v (w : G.Walk v v), Odd w.length → p.length ≤ w.length := by
  classical
  have hex : ∃ n, ∃ u, ∃ p : G.Walk u u, p.length = n ∧ Odd n := by
    have hw : ¬ ∀ u, ∀ p : G.Walk u u, Even p.length := by
      intro he; exact h (colorable_two_of_closed_walk_even he)
    push Not at hw
    obtain ⟨u, p, hp⟩ := hw
    exact ⟨p.length, u, p, rfl, Nat.not_even_iff_odd.mp hp⟩
  obtain ⟨u, p, hp, ho⟩ := Nat.find_spec hex
  refine ⟨u, p, hp.symm ▸ ho, ?_⟩
  intro v w hw
  rw [hp]
  exact Nat.find_min' hex ⟨v, w, rfl, hw⟩

theorem odd_closed_walk_length_ge_five (htri : G.CliqueFree 3)
    {u : V} (p : G.Walk u u) (ho : Odd p.length) : 5 ≤ p.length := by
  classical
  have hmod := Nat.odd_iff.mp ho
  have hne1 : p.length ≠ 1 := by
    intro h; exact (p.adj_of_length_eq_one h).ne rfl
  have hne3 : p.length ≠ 3 := by
    intro h
    have h01 := p.adj_getVert_succ (show 0 < p.length by omega)
    have h12 := p.adj_getVert_succ (show 1 < p.length by omega)
    have h20 := p.adj_getVert_succ (show 2 < p.length by omega)
    have hlast : p.getVert 3 = u := by simpa [h] using p.getVert_length
    simp only [Walk.getVert_zero] at h01
    rw [hlast] at h20
    exact htri {u, p.getVert 1, p.getVert 2}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨h01, h20.symm, h12⟩)
  omega

/-- The portion of a walk between two ordered time indices. -/
private def segment {u : V} (p : G.Walk u u) (i j : Nat) (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy rfl (by
    rw [Walk.drop_getVert, Nat.add_sub_of_le hij])

private theorem segment_length {u : V} (p : G.Walk u u) (i j : Nat)
    (hij : i ≤ j) (hj : j ≤ p.length) :
    (segment p i j hij).length = j - i := by
  simp [segment, Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega : j-i ≤ p.length-i)]

/-- Two neighbors of an outside vertex cut the odd walk into two closed
walks through that vertex. Minimality constrains their index difference. -/
theorem neighbor_index_gap {u : V} (p : G.Walk u u) (ho : Odd p.length)
    (hmin : ∀ v (w : G.Walk v v), Odd w.length → p.length ≤ w.length)
    (x : V) (i j : Nat) (hij : i ≤ j) (hj : j ≤ p.length)
    (hiAdj : G.Adj x (p.getVert i)) (hjAdj : G.Adj x (p.getVert j)) :
    ((j-i) % 2 = 0 → j-i ≤ 2) ∧
      ((j-i) % 2 = 1 → p.length ≤ j-i+2) := by
  let forward : G.Walk x x := ((segment p i j hij).concat hjAdj.symm).cons hiAdj
  let backward : G.Walk x x := (((p.drop j).append (p.take i)).concat hiAdj.symm).cons hjAdj
  have hf : forward.length = j-i+2 := by
    simp [forward, segment_length p i j hij hj, Nat.add_assoc]
  have hb : backward.length = p.length-j+i+2 := by
    simp [backward, Walk.take_length, Nat.min_eq_left (by omega : i ≤ p.length), Nat.add_assoc]
  constructor
  · intro he
    have hob : Odd backward.length := by
      rw [hb, Nat.odd_iff]
      have := Nat.odd_iff.mp ho
      omega
    have hm := hmin x backward hob
    rw [hb] at hm
    omega
  · intro hod
    have hof : Odd forward.length := by rw [hf, Nat.odd_iff]; omega
    have hm := hmin x forward hof
    rwa [hf] at hm

/-- Every vertex has at most two incidences with the positions of a
shortest odd closed walk of length at least five. The statement counts
positions directly, so it does not presuppose a separate cycle theorem. -/
theorem neighbor_positions_card_le_two [DecidableEq V] [DecidableRel G.Adj]
    {u : V} (p : G.Walk u u) (ho : Odd p.length) (hl : 5 ≤ p.length)
    (hmin : ∀ v (w : G.Walk v v), Odd w.length → p.length ≤ w.length)
    (x : V) :
    (Finset.univ.filter fun i : Fin p.length => G.Adj x (p.getVert i)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter fun i : Fin p.length => G.Adj x (p.getVert i)
  change S.card ≤ 2
  by_contra h
  have hcard : 2 < S.card := by omega
  let f := S.orderEmbOfFin rfl
  let a : Fin p.length := f ⟨0, by omega⟩
  let b : Fin p.length := f ⟨1, by omega⟩
  let d : Fin p.length := f ⟨2, by omega⟩
  have hab : a < b := f.strictMono (by change (0 : Nat) < 1; omega)
  have hbd : b < d := f.strictMono (by change (1 : Nat) < 2; omega)
  have ha : G.Adj x (p.getVert a) := by
    have hm : a ∈ S := S.orderEmbOfFin_mem rfl ⟨0, by omega⟩
    exact (Finset.mem_filter.mp hm).2
  have hb : G.Adj x (p.getVert b) := by
    have hm : b ∈ S := S.orderEmbOfFin_mem rfl ⟨1, by omega⟩
    exact (Finset.mem_filter.mp hm).2
  have hd : G.Adj x (p.getVert d) := by
    have hm : d ∈ S := S.orderEmbOfFin_mem rfl ⟨2, by omega⟩
    exact (Finset.mem_filter.mp hm).2
  have hab' : a.val < b.val := hab
  have hbd' : b.val < d.val := hbd
  have gab := neighbor_index_gap p ho hmin x a b (by omega) (by omega) ha hb
  have gbd := neighbor_index_gap p ho hmin x b d (by omega) (by omega) hb hd
  have gad := neighbor_index_gap p ho hmin x a d (by omega) (by omega) ha hd
  have haLt := a.isLt
  have hbLt := b.isLt
  have hdLt := d.isLt
  omega

/-- Double counting actual adjacency incidences along the odd walk. -/
theorem shortest_odd_walk_degree_sum_le [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u : V} (p : G.Walk u u) (ho : Odd p.length)
    (hl : 5 ≤ p.length)
    (hmin : ∀ v (w : G.Walk v v), Odd w.length → p.length ≤ w.length) :
    (∑ i : Fin p.length, G.degree (p.getVert i)) ≤ 2 * Fintype.card V := by
  classical
  have heq : (∑ i : Fin p.length, G.degree (p.getVert i)) =
      ∑ x : V, (Finset.univ.filter fun i : Fin p.length => G.Adj x (p.getVert i)).card := by
    calc
      _ = ∑ i : Fin p.length, ∑ x : V, if G.Adj x (p.getVert i) then (1 : Nat) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
        symm
        simpa only [Nat.cast_id, G.adj_comm] using
          (Finset.sum_boole (R := Nat) (fun x => G.Adj x (p.getVert i)) Finset.univ)
      _ = ∑ x : V, ∑ i : Fin p.length, if G.Adj x (p.getVert i) then (1 : Nat) else 0 :=
        Finset.sum_comm
      _ = _ := by simp only [Finset.sum_boole, Nat.cast_id]
  rw [heq]
  calc
    _ ≤ ∑ _x : V, 2 := Finset.sum_le_sum fun x _ =>
      neighbor_positions_card_le_two p ho hl hmin x
    _ = _ := by simp [Nat.mul_comm]

end DenseBipartite

/-- The triangle-free minimum-degree criterion needed by the synchronized
low/high cut argument. All graph structure is proved in Lean. -/
theorem triangleFree_isBipartite_of_dense [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : G.CliqueFree 3)
    (hdense : ∀ v, 2 * Fintype.card V < 5 * G.degree v) : G.Colorable 2 := by
  classical
  by_contra h
  obtain ⟨u, p, ho, hmin⟩ := DenseBipartite.exists_shortest_odd_closed_walk h
  have hl := DenseBipartite.odd_closed_walk_length_ge_five htri p ho
  have hupper := DenseBipartite.shortest_odd_walk_degree_sum_le p ho hl hmin
  have hstrict : p.length * (2 * Fintype.card V) <
      5 * (∑ i : Fin p.length, G.degree (p.getVert i)) := by
    have hs := Finset.sum_lt_sum
      (s := (Finset.univ : Finset (Fin p.length)))
      (f := fun _ : Fin p.length => 2 * Fintype.card V)
      (g := fun i : Fin p.length => 5 * G.degree (p.getVert i))
      (fun i _ => (hdense (p.getVert i)).le)
      ⟨⟨0, by omega⟩, Finset.mem_univ _, hdense _⟩
    simpa [Finset.mul_sum] using hs
  have hlength := Nat.mul_le_mul_left (2 * Fintype.card V) hl
  nlinarith

/-- Apply the general theorem to the actual low-color induced graph. -/
theorem synchronized_proper_low_bipartite (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hlow : (lowColorVertices c q).Nonempty)
    (hhigh : ((lowColorVertices c q)ᶜ).Nonempty) :
    ((colorGraph c q).induce (↑(lowColorVertices c q) : Set (Fin 61))).Colorable 2 := by
  classical
  letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
  apply triangleFree_isBipartite_of_dense
  · exact ((colorGraph c q).cliqueFree_induce_iff _ 3).mpr
      (colorGraph_cliqueFree_three c hc q).cliqueFreeOn
  · intro v
    have hd := synchronized_low_induced_degree c hc sync q v
    have hcsize : Fintype.card (↑(lowColorVertices c q) : Set (Fin 61)) =
        (lowColorVertices c q).card := Fintype.card_coe _
    rw [hcsize, hd]
    exact (synchronized_proper_cut_dense c hc sync q hlow hhigh).1

/-- Apply the same theorem to the physical high-color complement. -/
theorem synchronized_proper_high_bipartite (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hlow : (lowColorVertices c q).Nonempty)
    (hhigh : ((lowColorVertices c q)ᶜ).Nonempty) :
    ((colorGraph c q).induce (↑((lowColorVertices c q)ᶜ) : Set (Fin 61))).Colorable 2 := by
  classical
  letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
  apply triangleFree_isBipartite_of_dense
  · exact ((colorGraph c q).cliqueFree_induce_iff _ 3).mpr
      (colorGraph_cliqueFree_three c hc q).cliqueFreeOn
  · intro v
    have hd := synchronized_high_induced_degree c hc sync q v
    have hcsize : Fintype.card (↑((lowColorVertices c q)ᶜ) : Set (Fin 61)) =
        ((lowColorVertices c q)ᶜ).card := Fintype.card_coe _
    rw [hcsize, hd]
    have hnot14 : colorDegree c q v ≠ 14 := by simpa using v.property
    have hcases := synchronized_degree_cases c hc sync q v
    have h15 : 15 ≤ colorDegree c q v := by omega
    have hden := (synchronized_proper_cut_dense c hc sync q hlow hhigh).2
    omega


end Ramsey61
