import R4333Lean.Attaching61Arithmetic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Catalogue-free graph theory for the order-61 attaching-set route

This file advances the ordinary finite-combinatorial part of the
Fettes--Kramer--Radziszowski strategy.  It contains no catalogue premise and
no computational oracle.
-/

namespace R4333

open Finset SimpleGraph

universe u

/-! ## A small reusable two-colour Ramsey recurrence -/

/-- A graph is free of a red `K_k` and a blue `K_s`. -/
def TwoRamseyFree {V : Type*} (G : SimpleGraph V) (k s : ℕ) : Prop :=
  G.CliqueFree k ∧ Gᶜ.CliqueFree s

/-- Every graph on every finite type of cardinality at least `n` contains a
red `K_k` or a blue `K_s`. -/
def ForcesTwoCard (n k s : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V], n ≤ Fintype.card V →
    ∀ G : SimpleGraph V, ¬TwoRamseyFree G k s

@[simp]
theorem compl_induce_local (G : SimpleGraph α) (S : Set α) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext u v
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/-- The sharp elementary neighbourhood recurrence
`R(k+1,s+1) <= R(k,s+1)+R(k+1,s)`. -/
theorem forcesTwoCard_step {a b k s : ℕ}
    (hpos : 0 < a + b)
    (ha : ForcesTwoCard.{u} a k (s + 1))
    (hb : ForcesTwoCard.{u} b (k + 1) s) :
    ForcesTwoCard.{u} (a + b) (k + 1) (s + 1) := by
  classical
  intro V _ hcard G hfree
  have hVpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hVpos
  let v : V := Classical.choice inferInstance
  let NR : Set V := G.neighborSet v
  let NB : Set V := Gᶜ.neighborSet v
  have hsum :
      Fintype.card NR + Fintype.card NB = Fintype.card V - 1 := by
    rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard,
      Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    rw [← Finset.card_union_of_disjoint
      (Set.disjoint_toFinset.mpr (G.compl_neighborSet_disjoint v))]
    rw [← Set.toFinset_union]
    exact G.card_neighborSet_union_compl_neighborSet v
  have hlarge :
      a ≤ Fintype.card NR ∨ b ≤ Fintype.card NB := by
    omega
  rcases hlarge with hNR | hNB
  · have hredOn : G.CliqueFreeOn NR k := by
      have h := CliqueFreeOn.of_succ
        (G := G) (s := Set.univ) (n := k) (a := v)
        hfree.1.cliqueFreeOn (Set.mem_univ v)
      simpa [NR] using h
    have hNRfree : TwoRamseyFree (G.induce NR) k (s + 1) := by
      constructor
      · exact (G.cliqueFree_induce_iff NR k).2 hredOn
      · rw [compl_induce_local]
        exact (Gᶜ.cliqueFree_induce_iff NR (s + 1)).2
          hfree.2.cliqueFreeOn
    exact ha NR hNR (G.induce NR) hNRfree
  · have hblueOn : Gᶜ.CliqueFreeOn NB s := by
      have h := CliqueFreeOn.of_succ
        (G := Gᶜ) (s := Set.univ) (n := s) (a := v)
        hfree.2.cliqueFreeOn (Set.mem_univ v)
      simpa [NB] using h
    have hNBfree : TwoRamseyFree (G.induce NB) (k + 1) s := by
      constructor
      · exact (G.cliqueFree_induce_iff NB (k + 1)).2
          hfree.1.cliqueFreeOn
      · rw [compl_induce_local]
        exact (Gᶜ.cliqueFree_induce_iff NB s).2 hblueOn
    exact hb NB hNB (G.induce NB) hNBfree

/-- The elementary base `R(2,s) <= s`. -/
theorem forcesTwoCard_two_left (s : ℕ) : ForcesTwoCard.{u} s 2 s := by
  classical
  intro V _ hcard G hfree
  have hbot : G = ⊥ := (SimpleGraph.cliqueFree_two).1 hfree.1
  subst G
  have htop : ¬(⊤ : SimpleGraph V).CliqueFree s := by
    rw [SimpleGraph.not_cliqueFree_iff_top_isContained]
    let f : Fin s ↪ V :=
      (Fin.castLEEmb hcard).trans (Fintype.equivFin V).symm.toEmbedding
    exact (SimpleGraph.Embedding.completeGraph f).isContained
  exact htop (by simpa using hfree.2)

/-- The symmetric base `R(k,2) <= k`. -/
theorem forcesTwoCard_two_right (k : ℕ) : ForcesTwoCard.{u} k k 2 := by
  classical
  intro V _ hcard G hfree
  have hcomplbot : Gᶜ = ⊥ := (SimpleGraph.cliqueFree_two).1 hfree.2
  have htop : G = ⊤ := by
    apply compl_injective
    simpa using hcomplbot
  subst G
  have hnot : ¬(⊤ : SimpleGraph V).CliqueFree k := by
    rw [SimpleGraph.not_cliqueFree_iff_top_isContained]
    let f : Fin k ↪ V :=
      (Fin.castLEEmb hcard).trans (Fintype.equivFin V).symm.toEmbedding
    exact (SimpleGraph.Embedding.completeGraph f).isContained
  exact hnot hfree.1

/-- The direct two-colour Ramsey fact used in every cross-intersection. -/
theorem forcesTwoCard_6_3_3 : ForcesTwoCard.{u} 6 3 3 := by
  simpa using forcesTwoCard_step (by omega)
    (forcesTwoCard_two_left 3) (forcesTwoCard_two_right 3)

/-- The elementary recurrence chain `R(3,7) <= 28`. -/
theorem forcesTwoCard_28_3_7 : ForcesTwoCard.{u} 28 3 7 := by
  have h34 : ForcesTwoCard.{u} 10 3 4 := by
    simpa using forcesTwoCard_step (by omega)
      (forcesTwoCard_two_left 4) forcesTwoCard_6_3_3
  have h35 : ForcesTwoCard.{u} 15 3 5 := by
    simpa using forcesTwoCard_step (by omega)
      (forcesTwoCard_two_left 5) h34
  have h36 : ForcesTwoCard.{u} 21 3 6 := by
    simpa using forcesTwoCard_step (by omega)
      (forcesTwoCard_two_left 6) h35
  simpa using forcesTwoCard_step (by omega)
    (forcesTwoCard_two_left 7) h36

/-- A triangle-free graph on at least 28 vertices contains an independent
set of seven vertices, returned as an explicit embedding. -/
theorem triangleFree_exists_independent7 {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hcard : 28 ≤ Fintype.card V)
    (htri : G.CliqueFree 3) :
    ∃ f : Fin 7 ↪ V, ∀ {i j}, i ≠ j → ¬G.Adj (f i) (f j) := by
  classical
  have hnot : ¬Gᶜ.CliqueFree 7 := by
    intro hblue
    exact forcesTwoCard_28_3_7 V hcard G ⟨htri, hblue⟩
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hnot
  refine ⟨e.toEmbedding, ?_⟩
  intro i j hij hadj
  have hcomp : Gᶜ.Adj (e i) (e j) := by
    exact e.map_rel_iff.mpr (by simpa using hij)
  have hpair : e i ≠ e j ∧ ¬G.Adj (e i) (e j) := by
    simpa [SimpleGraph.compl_adj] using hcomp
  exact hpair.2 hadj

/-! ## Finite colour neighbourhoods -/

/-- The vertices joined to `v` by an edge of colour `q`.  The diagonal is
removed explicitly because `EdgeColoring` deliberately leaves it irrelevant. -/
def colorNeighborhood {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (q : C) (v : V) : Finset V :=
  Finset.univ.filter fun w ↦ w ≠ v ∧ c v w = q

/-- Colour degree as the cardinality of the finite colour neighbourhood. -/
def colorDegree {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (q : C) (v : V) : ℕ :=
  #(colorNeighborhood c q v)

@[simp]
theorem mem_colorNeighborhood {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (q : C) (v w : V) :
    w ∈ colorNeighborhood c q v ↔ w ≠ v ∧ c v w = q := by
  simp [colorNeighborhood]

theorem colorNeighborhood_symm {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (q : C) (v w : V)
    (hvw : v ≠ w) :
    w ∈ colorNeighborhood c q v ↔ v ∈ colorNeighborhood c q w := by
  simp only [mem_colorNeighborhood, hvw, ne_eq, Ne.symm hvw]
  exact c.color_symm v w ▸ Iff.rfl

/-- The colour neighbourhoods partition all vertices other than the centre. -/
theorem sum_colorDegree_eq_card_sub_one {V C : Type*} [Fintype V]
    [Fintype C] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (v : V) :
    (∑ q : C, colorDegree c q v) = Fintype.card V - 1 := by
  classical
  have hpartition :
      #((Finset.univ : Finset V).erase v) =
        ∑ q ∈ (Finset.univ : Finset C),
          #{w ∈ (Finset.univ : Finset V).erase v | c v w = q} :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
  calc
    (∑ q : C, colorDegree c q v) =
        ∑ q ∈ (Finset.univ : Finset C),
          #{w ∈ (Finset.univ : Finset V).erase v | c v w = q} := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [colorDegree]
      congr 1
      ext w
      simp [colorNeighborhood]
    _ = #((Finset.univ : Finset V).erase v) := hpartition.symm
    _ = Fintype.card V - 1 := by simp

/-- The preceding partition, written as the concrete four degree entries. -/
theorem fourColor_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (v : V) :
    colorDegree c (false, false) v + colorDegree c (false, true) v +
      colorDegree c (true, false) v + colorDegree c (true, true) v =
        Fintype.card V - 1 := by
  simpa [FourColor, Fintype.sum_prod_type, Fintype.sum_bool,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      sum_colorDegree_eq_card_sub_one c v

/-! ## Small induced colour sets -/

/-- The ordinary graph consisting of the edges of one selected colour. -/
def colorGraph {V C : Type*} [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (q : C) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c x y = q
  symm := ⟨fun x y h ↦
    ⟨h.1.symm, (c.color_symm x y).symm.trans h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Each single-colour graph is triangle-free when the edge colouring has
no monochromatic triangle. -/
theorem colorGraph_cliqueFree_three {V C : Type*} [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (q : C) : (colorGraph c q).CliqueFree 3 := by
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs.card_eq
  have hxmem : x ∈ ({x, y, z} : Finset V) := by simp
  have hymem : y ∈ ({x, y, z} : Finset V) := by simp
  have hzmem : z ∈ ({x, y, z} : Finset V) := by simp
  have axy : (colorGraph c q).Adj x y :=
    hs.isClique hxmem hymem hxy
  have axz : (colorGraph c q).Adj x z :=
    hs.isClique hxmem hzmem hxz
  have ayz : (colorGraph c q).Adj y z :=
    hs.isClique hymem hzmem hyz
  change _ ∧ _ at axy axz ayz
  apply hc x y z
  · exact ⟨hxy, hxz, hyz⟩
  · exact ⟨axy.2.trans axz.2.symm, axz.2.trans ayz.2.symm⟩

/-- An explicitly two-coloured vertex set has at most five vertices.  This
is the finite-set form of `R(3,3) <= 6` used by the attaching argument. -/
theorem twoColorFinset_card_le_five {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    {p q : C} (S : Finset V)
    (hcolors : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y →
      c x y = p ∨ c x y = q) :
    #S ≤ 5 := by
  classical
  by_contra hnot
  have hcard : 6 ≤ Fintype.card {x // x ∈ S} := by
    have hScard : 6 ≤ #S := by omega
    simpa using hScard
  let G : SimpleGraph {x // x ∈ S} :=
    (colorGraph c p).induce (↑S : Set V)
  have hred : G.CliqueFree 3 := by
    exact ((colorGraph c p).cliqueFree_induce_iff (↑S : Set V) 3).2
      (colorGraph_cliqueFree_three c hc p).cliqueFreeOn
  have hblue : Gᶜ.CliqueFree 3 := by
    intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
    have hxmem : x ∈ ({x, y, z} : Finset {x // x ∈ S}) := by simp
    have hymem : y ∈ ({x, y, z} : Finset {x // x ∈ S}) := by simp
    have hzmem : z ∈ ({x, y, z} : Finset {x // x ∈ S}) := by simp
    have axy : Gᶜ.Adj x y := ht.isClique hxmem hymem hxy
    have axz : Gᶜ.Adj x z := ht.isClique hxmem hzmem hxz
    have ayz : Gᶜ.Adj y z := ht.isClique hymem hzmem hyz
    have edge_is_q (a b : {x // x ∈ S}) (hab : a ≠ b)
        (hcomp : Gᶜ.Adj a b) : c a b = q := by
      have hnotp : c a b ≠ p := by
        intro hp
        have hadj : G.Adj a b := by
          change a.val ≠ b.val ∧ c a.val b.val = p
          exact ⟨Subtype.val_injective.ne hab, hp⟩
        exact ((G.compl_adj a b).mp hcomp).2 hadj
      rcases hcolors a.property b.property
          (Subtype.val_injective.ne hab) with hp | hq
      · exact (hnotp hp).elim
      · exact hq
    have cxy : c x y = q := edge_is_q x y hxy axy
    have cxz : c x z = q := edge_is_q x z hxz axz
    have cyz : c y z = q := edge_is_q y z hyz ayz
    apply hc x y z
    · exact ⟨Subtype.val_injective.ne hxy, Subtype.val_injective.ne hxz,
        Subtype.val_injective.ne hyz⟩
    · exact ⟨cxy.trans cxz.symm, cxz.trans cyz.symm⟩
  exact forcesTwoCard_6_3_3 _ hcard G ⟨hred, hblue⟩

/-- An explicitly three-coloured vertex set has at most sixteen vertices.
This is a direct, catalogue-free proof of the `R(3,3,3) <= 17` fact needed
to bound a colour neighbourhood in a four-colouring. -/
theorem threeColorFinset_card_le_sixteen {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (p q r : C) (S : Finset V)
    (hcolors : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y →
      c x y = p ∨ c x y = q ∨ c x y = r) :
    #S ≤ 16 := by
  classical
  by_contra hnot
  have hScard : 17 ≤ #S := by omega
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hSnonempty
  let T : Finset V := S.erase v
  let F (a : C) : Finset V := T.filter fun w ↦ c v w = a
  have hfiber (a b d : C)
      (hremainder : ∀ {z : C}, (z = p ∨ z = q ∨ z = r) → z ≠ a →
        z = b ∨ z = d) :
      #(F a) ≤ 5 := by
    apply twoColorFinset_card_le_five c hc (p := b) (q := d) (F a)
    intro x hx y hy hxy
    have hxfilter := (Finset.mem_filter.mp hx)
    have hyfilter := (Finset.mem_filter.mp hy)
    have hxerase := (Finset.mem_erase.mp hxfilter.1)
    have hyerase := (Finset.mem_erase.mp hyfilter.1)
    have hxS : x ∈ S := hxerase.2
    have hyS : y ∈ S := hyerase.2
    have hnot_a : c x y ≠ a := by
      intro hxy_a
      apply hc v x y
      · exact ⟨hxerase.1.symm, hyerase.1.symm, hxy⟩
      · exact ⟨hxfilter.2.trans hyfilter.2.symm,
          hyfilter.2.trans hxy_a.symm⟩
    exact hremainder (hcolors hxS hyS hxy) hnot_a
  have hp : #(F p) ≤ 5 := by
    apply hfiber p q r
    intro z hz hne
    rcases hz with hz | hz | hz
    · exact (hne hz).elim
    · exact Or.inl hz
    · exact Or.inr hz
  have hq : #(F q) ≤ 5 := by
    apply hfiber q p r
    intro z hz hne
    rcases hz with hz | hz | hz
    · exact Or.inl hz
    · exact (hne hz).elim
    · exact Or.inr hz
  have hr : #(F r) ≤ 5 := by
    apply hfiber r p q
    intro z hz hne
    rcases hz with hz | hz | hz
    · exact Or.inl hz
    · exact Or.inr hz
    · exact (hne hz).elim
  let K : Finset C := {p, q, r}
  have hmaps : (T : Set V).MapsTo (fun w ↦ c v w) K := by
    intro w hw
    have hwerase := Finset.mem_erase.mp hw
    have hwcolors := hcolors hv hwerase.2 hwerase.1.symm
    simpa [K] using hwcolors
  have hpartition : #T = ∑ a ∈ K, #(F a) := by
    simpa [F] using (Finset.card_eq_sum_card_fiberwise hmaps)
  have hKcard : #K ≤ 3 := by
    have h1 : #({p, q, r} : Finset C) ≤ #({q, r} : Finset C) + 1 :=
      Finset.card_insert_le p {q, r}
    have h2 : #({q, r} : Finset C) ≤ #({r} : Finset C) + 1 :=
      Finset.card_insert_le q {r}
    have h3 : #({r} : Finset C) = 1 := by simp
    simpa [K] using (show #({p, q, r} : Finset C) ≤ 3 by omega)
  have hfiber_bound : ∀ a ∈ K, #(F a) ≤ 5 := by
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hTcard : #T ≤ 15 := by
    calc
      #T = ∑ a ∈ K, #(F a) := hpartition
      _ ≤ ∑ _a ∈ K, 5 := Finset.sum_le_sum hfiber_bound
      _ = #K * 5 := by simp
      _ ≤ 15 := by omega
  have herase : #T + 1 = #S := by
    simpa [T] using Finset.card_erase_add_one hv
  omega

/-- A colour neighbourhood never contains an internal edge of its defining
colour in a triangle-free colouring. -/
theorem neighborhood_avoids_own_color {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    {q : C} {v x y : V}
    (hx : x ∈ colorNeighborhood c q v)
    (hy : y ∈ colorNeighborhood c q v) (hxy : x ≠ y) :
    c x y ≠ q := by
  intro hcolor
  have hx' := (mem_colorNeighborhood c q v x).1 hx
  have hy' := (mem_colorNeighborhood c q v y).1 hy
  apply hc v x y
  · exact ⟨hx'.1.symm, hy'.1.symm, hxy⟩
  · exact ⟨hx'.2.trans hy'.2.symm,
      hy'.2.trans hcolor.symm⟩

/-- If four named colours exhaust the colour type, then the neighbourhood
in the first colour has size at most sixteen. -/
theorem colorDegree_le_sixteen_of_four {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (a b d e : C) (hexhaust : ∀ z : C, z = a ∨ z = b ∨ z = d ∨ z = e)
    (v : V) :
    colorDegree c a v ≤ 16 := by
  apply threeColorFinset_card_le_sixteen c hc b d e
      (colorNeighborhood c a v)
  intro x hx y hy hxy
  have hnot_a := neighborhood_avoids_own_color c hc hx hy hxy
  rcases hexhaust (c x y) with ha | hb | hd | he
  · exact (hnot_a ha).elim
  · exact Or.inl hb
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr he)

/-- In a triangle-free four-colouring every colour degree is at most 16.
This is the exact local consequence of the direct `R(3,3,3) <= 17` proof. -/
theorem fourColor_colorDegree_le_sixteen {V : Type*} [Fintype V]
    [DecidableEq V] (c : EdgeColoring V FourColor)
    (hc : NoMonochromaticTriangle c) (q : FourColor) (v : V) :
    colorDegree c q v ≤ 16 := by
  rcases q with ⟨q₁, q₂⟩
  cases q₁ <;> cases q₂
  · apply colorDegree_le_sixteen_of_four c hc
      (false, false) (false, true) (true, false) (true, true)
    intro z
    rcases z with ⟨z₁, z₂⟩
    cases z₁ <;> cases z₂ <;> simp
  · apply colorDegree_le_sixteen_of_four c hc
      (false, true) (false, false) (true, false) (true, true)
    intro z
    rcases z with ⟨z₁, z₂⟩
    cases z₁ <;> cases z₂ <;> simp
  · apply colorDegree_le_sixteen_of_four c hc
      (true, false) (false, false) (false, true) (true, true)
    intro z
    rcases z with ⟨z₁, z₂⟩
    cases z₁ <;> cases z₂ <;> simp
  · apply colorDegree_le_sixteen_of_four c hc
      (true, true) (false, false) (false, true) (true, false)
    intro z
    rcases z with ⟨z₁, z₂⟩
    cases z₁ <;> cases z₂ <;> simp

/-- On 61 vertices, at most one colour at any vertex can have degree at
most 13.  This packages the degree partition and the local degree-16 bound
into the hypothesis needed by the bad-pair graph. -/
theorem fourColor_smallColor_unique_at_61 {V : Type*} [Fintype V]
    [DecidableEq V] (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (v : V) (q r : FourColor)
    (hq : colorDegree c q v ≤ 13) (hr : colorDegree c r v ≤ 13) :
    q = r := by
  have h00 := fourColor_colorDegree_le_sixteen c hc (false, false) v
  have h01 := fourColor_colorDegree_le_sixteen c hc (false, true) v
  have h10 := fourColor_colorDegree_le_sixteen c hc (true, false) v
  have h11 := fourColor_colorDegree_le_sixteen c hc (true, true) v
  have hsum := fourColor_degree_sum c v
  rw [hcard] at hsum
  fin_cases q <;> fin_cases r <;> simp_all <;> omega

/-- Vertices at which a fixed colour has degree at least `lower`. -/
def largeVertices {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (lower : ℕ) (q : C) : Finset V :=
  Finset.univ.filter fun v ↦ lower ≤ colorDegree c q v

@[simp]
theorem mem_largeVertices {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C]
    (c : EdgeColoring V C) (lower : ℕ) (q : C) (v : V) :
    v ∈ largeVertices c lower q ↔ lower ≤ colorDegree c q v := by
  simp [largeVertices]

/-- Every vertex at order 61 has two distinct colours of degree at least 15. -/
theorem fourColor_two_large_at_61 {V : Type*} [Fintype V]
    [DecidableEq V] (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (v : V) :
    ∃ q r : FourColor, q ≠ r ∧
      15 ≤ colorDegree c q v ∧ 15 ≤ colorDegree c r v := by
  have h00 := fourColor_colorDegree_le_sixteen c hc (false, false) v
  have h01 := fourColor_colorDegree_le_sixteen c hc (false, true) v
  have h10 := fourColor_colorDegree_le_sixteen c hc (true, false) v
  have h11 := fourColor_colorDegree_le_sixteen c hc (true, true) v
  have hsum := fourColor_degree_sum c v
  rw [hcard] at hsum
  rcases degree61_two_ge_fifteen
      (colorDegree c (false, false) v)
      (colorDegree c (false, true) v)
      (colorDegree c (true, false) v)
      (colorDegree c (true, true) v)
      h00 h01 h10 h11 (by omega) with h | h | h | h | h | h
  · exact ⟨(false, false), (false, true), by simp, h⟩
  · exact ⟨(false, false), (true, false), by simp, h⟩
  · exact ⟨(false, false), (true, true), by simp, h⟩
  · exact ⟨(false, true), (true, false), by simp, h⟩
  · exact ⟨(false, true), (true, true), by simp, h⟩
  · exact ⟨(true, false), (true, true), by simp, h⟩

/-- Double-counting the large-colour incidences gives at least 122 such
incidences at order 61. -/
theorem fourColor_largeIncidences_ge_122 {V : Type*} [Fintype V]
    [DecidableEq V] (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    122 ≤ ∑ q : FourColor, #(largeVertices c 15 q) := by
  classical
  have hlocal (v : V) :
      2 ≤ #((Finset.univ : Finset FourColor).filter fun q ↦
        15 ≤ colorDegree c q v) := by
    obtain ⟨q, r, hqr, hq, hr⟩ := fourColor_two_large_at_61 hcard c hc v
    have hsub : ({q, r} : Finset FourColor) ⊆
        (Finset.univ : Finset FourColor).filter fun a ↦
          15 ≤ colorDegree c a v := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl
      · exact hq
      · exact hr
    have hpair : #({q, r} : Finset FourColor) = 2 :=
      Finset.card_pair_eq_two_iff.mpr hqr
    rw [← hpair]
    exact Finset.card_le_card hsub
  have hdouble :
      (∑ v : V, #((Finset.univ : Finset FourColor).filter fun q ↦
          15 ≤ colorDegree c q v)) =
        ∑ q : FourColor, #(largeVertices c 15 q) := by
    calc
      (∑ v : V, #((Finset.univ : Finset FourColor).filter fun q ↦
          15 ≤ colorDegree c q v)) =
          ∑ v : V, ∑ q : FourColor,
            if 15 ≤ colorDegree c q v then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.card_eq_sum_ones]
              simp only [Finset.sum_filter]
      _ = ∑ q : FourColor, ∑ v : V,
            if 15 ≤ colorDegree c q v then 1 else 0 := Finset.sum_comm
      _ = ∑ q : FourColor, #(largeVertices c 15 q) := by
            apply Finset.sum_congr rfl
            intro q _
            rw [Finset.card_eq_sum_ones]
            simp only [largeVertices, Finset.sum_filter]
  calc
    122 = ∑ _v : V, 2 := by simp [hcard]
    _ ≤ ∑ v : V, #((Finset.univ : Finset FourColor).filter fun q ↦
        15 ≤ colorDegree c q v) := Finset.sum_le_sum fun v _ ↦ hlocal v
    _ = ∑ q : FourColor, #(largeVertices c 15 q) := hdouble

/-- Hence one colour is large at at least 31 vertices. -/
theorem exists_fourColor_largeVertices_31 {V : Type*} [Fintype V]
    [DecidableEq V] (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ q : FourColor, 31 ≤ #(largeVertices c 15 q) := by
  have hsum := fourColor_largeIncidences_ge_122 hcard c hc
  have hexpanded :
      122 ≤ #(largeVertices c 15 (false, false)) +
        #(largeVertices c 15 (false, true)) +
        #(largeVertices c 15 (true, false)) +
        #(largeVertices c 15 (true, true)) := by
    simpa [FourColor, Fintype.sum_prod_type, Fintype.sum_bool,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
  rcases largeIncidence_pigeonhole31
      #(largeVertices c 15 (false, false))
      #(largeVertices c 15 (false, true))
      #(largeVertices c 15 (true, false))
      #(largeVertices c 15 (true, true)) hexpanded with h | h | h | h
  · exact ⟨(false, false), h⟩
  · exact ⟨(false, true), h⟩
  · exact ⟨(true, false), h⟩
  · exact ⟨(true, true), h⟩

/-- The graph of pairs whose edge colour is small at both endpoints. -/
def badPairGraph {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (small : ℕ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ colorDegree c (c x y) x ≤ small ∧
    colorDegree c (c x y) y ≤ small
  symm := ⟨fun x y h ↦ by
    rw [← c.color_symm x y]
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h ↦ h.1 rfl⟩

/-- If every vertex has at most one small colour, the bad-pair graph is
triangle-free. -/
theorem badPairGraph_cliqueFree_three {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c) (small : ℕ)
    (hunique : ∀ v q r,
      colorDegree c q v ≤ small → colorDegree c r v ≤ small → q = r) :
    (badPairGraph c small).CliqueFree 3 := by
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs.card_eq
  have hxmem : x ∈ ({x, y, z} : Finset V) := by simp
  have hymem : y ∈ ({x, y, z} : Finset V) := by simp
  have hzmem : z ∈ ({x, y, z} : Finset V) := by simp
  have axy : (badPairGraph c small).Adj x y :=
    hs.isClique hxmem hymem hxy
  have axz : (badPairGraph c small).Adj x z :=
    hs.isClique hxmem hzmem hxz
  have ayz : (badPairGraph c small).Adj y z :=
    hs.isClique hymem hzmem hyz
  change _ ∧ _ ∧ _ at axy axz ayz
  have hcx : c x y = c x z := hunique x _ _ axy.2.1 axz.2.1
  have hcy : c x y = c y z := by
    apply hunique y
    · simpa [c.color_symm x y] using axy.2.2
    · exact ayz.2.1
  apply hc x y z
  · exact ⟨hxy, hxz, hyz⟩
  · exact ⟨hcx, hcx.symm.trans hcy⟩

/-- The concrete bad-pair graph of a hypothetical order-61 four-colouring
is triangle-free, with no catalogue or search premise. -/
theorem badPairGraph_fourColor_cliqueFree_three_at_61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    (badPairGraph c 13).CliqueFree 3 := by
  apply badPairGraph_cliqueFree_three c hc 13
  intro v q r hq hr
  exact fourColor_smallColor_unique_at_61 hcard c hc v q r hq hr

/-- Consequently there are seven explicitly indexed vertices such that no
pair is simultaneously small in its edge colour at both endpoints. -/
theorem exists_seven_pairwise_nonbad_at_61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ f : Fin 7 ↪ V, ∀ {i j}, i ≠ j →
      ¬(badPairGraph c 13).Adj (f i) (f j) := by
  apply triangleFree_exists_independent7 (badPairGraph c 13)
  · omega
  · exact badPairGraph_fourColor_cliqueFree_three_at_61 hcard c hc

/-- The seven nonbad vertices can be chosen inside one fixed colour's
degree-at-least-15 set.  This is the complete selection stage preceding the
seven-neighbourhood overlap count. -/
theorem exists_largeColor_seven_pairwise_nonbad_at_61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ q : FourColor, ∃ f : Fin 7 ↪ V,
      (∀ i, 15 ≤ colorDegree c q (f i)) ∧
      ∀ {i j}, i ≠ j → ¬(badPairGraph c 13).Adj (f i) (f j) := by
  classical
  obtain ⟨q, hqcard⟩ := exists_fourColor_largeVertices_31 hcard c hc
  let L : Finset V := largeVertices c 15 q
  let G : SimpleGraph {v // v ∈ L} :=
    (badPairGraph c 13).induce (↑L : Set V)
  have hLcard : 28 ≤ Fintype.card {v // v ∈ L} := by
    have : 28 ≤ #L := by simpa [L] using hqcard.trans' (by omega)
    simpa using this
  have hGtri : G.CliqueFree 3 := by
    exact ((badPairGraph c 13).cliqueFree_induce_iff (↑L : Set V) 3).2
      (badPairGraph_fourColor_cliqueFree_three_at_61 hcard c hc).cliqueFreeOn
  obtain ⟨e, he⟩ := triangleFree_exists_independent7 G hLcard hGtri
  let inclusion : {v // v ∈ L} ↪ V := Function.Embedding.subtype _
  let f : Fin 7 ↪ V := e.trans inclusion
  refine ⟨q, f, ?_, ?_⟩
  · intro i
    have hi : f i ∈ L := (e i).property
    simpa [L] using hi
  · intro i j hij hadj
    apply he hij
    exact hadj

/-- Seven 15-subsets of a universe of size at most 61 cannot have every
pairwise intersection of size at most two.  This is the set-theoretic form
of the `15+13+11+9+7+5+3=63` argument. -/
theorem seven_large_finsets_overlap_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V ≤ 61) (S : Fin 7 → Finset V)
    (hsize : ∀ i, 15 ≤ #(S i)) :
    ∃ i j : Fin 7, i ≠ j ∧ 3 ≤ #(S i ∩ S j) := by
  classical
  by_contra hnone
  have hsmall (i j : Fin 7) (hij : i ≠ j) : #(S i ∩ S j) ≤ 2 := by
    by_contra hnot
    apply hnone
    exact ⟨i, j, hij, by omega⟩
  let S0 := S (0 : Fin 7)
  let S1 := S (1 : Fin 7)
  let S2 := S (2 : Fin 7)
  let S3 := S (3 : Fin 7)
  let S4 := S (4 : Fin 7)
  let S5 := S (5 : Fin 7)
  let S6 := S (6 : Fin 7)
  let U0 := S0
  let U1 := U0 ∪ S1
  let U2 := U1 ∪ S2
  let U3 := U2 ∪ S3
  let U4 := U3 ∪ S4
  let U5 := U4 ∪ S5
  let U6 := U5 ∪ S6
  have hinter_union (A U B : Finset V) :
      #(A ∩ (U ∪ B)) ≤ #(A ∩ U) + #(A ∩ B) := by
    rw [Finset.inter_union_distrib_left]
    exact Finset.card_union_le _ _
  have h10 : #(S1 ∩ S0) ≤ 2 := by
    simpa [S1, S0] using hsmall (1 : Fin 7) (0 : Fin 7) (by decide)
  have h20 : #(S2 ∩ S0) ≤ 2 := by
    simpa [S2, S0] using hsmall (2 : Fin 7) (0 : Fin 7) (by decide)
  have h21 : #(S2 ∩ S1) ≤ 2 := by
    simpa [S2, S1] using hsmall (2 : Fin 7) (1 : Fin 7) (by decide)
  have h30 : #(S3 ∩ S0) ≤ 2 := by
    simpa [S3, S0] using hsmall (3 : Fin 7) (0 : Fin 7) (by decide)
  have h31 : #(S3 ∩ S1) ≤ 2 := by
    simpa [S3, S1] using hsmall (3 : Fin 7) (1 : Fin 7) (by decide)
  have h32 : #(S3 ∩ S2) ≤ 2 := by
    simpa [S3, S2] using hsmall (3 : Fin 7) (2 : Fin 7) (by decide)
  have h40 : #(S4 ∩ S0) ≤ 2 := by
    simpa [S4, S0] using hsmall (4 : Fin 7) (0 : Fin 7) (by decide)
  have h41 : #(S4 ∩ S1) ≤ 2 := by
    simpa [S4, S1] using hsmall (4 : Fin 7) (1 : Fin 7) (by decide)
  have h42 : #(S4 ∩ S2) ≤ 2 := by
    simpa [S4, S2] using hsmall (4 : Fin 7) (2 : Fin 7) (by decide)
  have h43 : #(S4 ∩ S3) ≤ 2 := by
    simpa [S4, S3] using hsmall (4 : Fin 7) (3 : Fin 7) (by decide)
  have h50 : #(S5 ∩ S0) ≤ 2 := by
    simpa [S5, S0] using hsmall (5 : Fin 7) (0 : Fin 7) (by decide)
  have h51 : #(S5 ∩ S1) ≤ 2 := by
    simpa [S5, S1] using hsmall (5 : Fin 7) (1 : Fin 7) (by decide)
  have h52 : #(S5 ∩ S2) ≤ 2 := by
    simpa [S5, S2] using hsmall (5 : Fin 7) (2 : Fin 7) (by decide)
  have h53 : #(S5 ∩ S3) ≤ 2 := by
    simpa [S5, S3] using hsmall (5 : Fin 7) (3 : Fin 7) (by decide)
  have h54 : #(S5 ∩ S4) ≤ 2 := by
    simpa [S5, S4] using hsmall (5 : Fin 7) (4 : Fin 7) (by decide)
  have h60 : #(S6 ∩ S0) ≤ 2 := by
    simpa [S6, S0] using hsmall (6 : Fin 7) (0 : Fin 7) (by decide)
  have h61 : #(S6 ∩ S1) ≤ 2 := by
    simpa [S6, S1] using hsmall (6 : Fin 7) (1 : Fin 7) (by decide)
  have h62 : #(S6 ∩ S2) ≤ 2 := by
    simpa [S6, S2] using hsmall (6 : Fin 7) (2 : Fin 7) (by decide)
  have h63 : #(S6 ∩ S3) ≤ 2 := by
    simpa [S6, S3] using hsmall (6 : Fin 7) (3 : Fin 7) (by decide)
  have h64 : #(S6 ∩ S4) ≤ 2 := by
    simpa [S6, S4] using hsmall (6 : Fin 7) (4 : Fin 7) (by decide)
  have h65 : #(S6 ∩ S5) ≤ 2 := by
    simpa [S6, S5] using hsmall (6 : Fin 7) (5 : Fin 7) (by decide)
  have hI1 : #(S1 ∩ U0) ≤ 2 := by simpa [U0] using h10
  have hI2 : #(S2 ∩ U1) ≤ 4 := by
    calc
      #(S2 ∩ U1) ≤ #(S2 ∩ U0) + #(S2 ∩ S1) := by
        simpa [U1] using hinter_union S2 U0 S1
      _ ≤ 4 := by simpa [U0] using Nat.add_le_add h20 h21
  have hI3U1 : #(S3 ∩ U1) ≤ 4 := by
    calc
      #(S3 ∩ U1) ≤ #(S3 ∩ U0) + #(S3 ∩ S1) := by
        simpa [U1] using hinter_union S3 U0 S1
      _ ≤ 4 := by simpa [U0] using Nat.add_le_add h30 h31
  have hI3 : #(S3 ∩ U2) ≤ 6 := by
    calc
      #(S3 ∩ U2) ≤ #(S3 ∩ U1) + #(S3 ∩ S2) := by
        simpa [U2] using hinter_union S3 U1 S2
      _ ≤ 6 := by omega
  have hI4U1 : #(S4 ∩ U1) ≤ 4 := by
    calc
      #(S4 ∩ U1) ≤ #(S4 ∩ U0) + #(S4 ∩ S1) := by
        simpa [U1] using hinter_union S4 U0 S1
      _ ≤ 4 := by simpa [U0] using Nat.add_le_add h40 h41
  have hI4U2 : #(S4 ∩ U2) ≤ 6 := by
    calc
      #(S4 ∩ U2) ≤ #(S4 ∩ U1) + #(S4 ∩ S2) := by
        simpa [U2] using hinter_union S4 U1 S2
      _ ≤ 6 := by omega
  have hI4 : #(S4 ∩ U3) ≤ 8 := by
    calc
      #(S4 ∩ U3) ≤ #(S4 ∩ U2) + #(S4 ∩ S3) := by
        simpa [U3] using hinter_union S4 U2 S3
      _ ≤ 8 := by omega
  have hI5U1 : #(S5 ∩ U1) ≤ 4 := by
    calc
      #(S5 ∩ U1) ≤ #(S5 ∩ U0) + #(S5 ∩ S1) := by
        simpa [U1] using hinter_union S5 U0 S1
      _ ≤ 4 := by simpa [U0] using Nat.add_le_add h50 h51
  have hI5U2 : #(S5 ∩ U2) ≤ 6 := by
    calc
      #(S5 ∩ U2) ≤ #(S5 ∩ U1) + #(S5 ∩ S2) := by
        simpa [U2] using hinter_union S5 U1 S2
      _ ≤ 6 := by omega
  have hI5U3 : #(S5 ∩ U3) ≤ 8 := by
    calc
      #(S5 ∩ U3) ≤ #(S5 ∩ U2) + #(S5 ∩ S3) := by
        simpa [U3] using hinter_union S5 U2 S3
      _ ≤ 8 := by omega
  have hI5 : #(S5 ∩ U4) ≤ 10 := by
    calc
      #(S5 ∩ U4) ≤ #(S5 ∩ U3) + #(S5 ∩ S4) := by
        simpa [U4] using hinter_union S5 U3 S4
      _ ≤ 10 := by omega
  have hI6U1 : #(S6 ∩ U1) ≤ 4 := by
    calc
      #(S6 ∩ U1) ≤ #(S6 ∩ U0) + #(S6 ∩ S1) := by
        simpa [U1] using hinter_union S6 U0 S1
      _ ≤ 4 := by simpa [U0] using Nat.add_le_add h60 h61
  have hI6U2 : #(S6 ∩ U2) ≤ 6 := by
    calc
      #(S6 ∩ U2) ≤ #(S6 ∩ U1) + #(S6 ∩ S2) := by
        simpa [U2] using hinter_union S6 U1 S2
      _ ≤ 6 := by omega
  have hI6U3 : #(S6 ∩ U3) ≤ 8 := by
    calc
      #(S6 ∩ U3) ≤ #(S6 ∩ U2) + #(S6 ∩ S3) := by
        simpa [U3] using hinter_union S6 U2 S3
      _ ≤ 8 := by omega
  have hI6U4 : #(S6 ∩ U4) ≤ 10 := by
    calc
      #(S6 ∩ U4) ≤ #(S6 ∩ U3) + #(S6 ∩ S4) := by
        simpa [U4] using hinter_union S6 U3 S4
      _ ≤ 10 := by omega
  have hI6 : #(S6 ∩ U5) ≤ 12 := by
    calc
      #(S6 ∩ U5) ≤ #(S6 ∩ U4) + #(S6 ∩ S5) := by
        simpa [U5] using hinter_union S6 U4 S5
      _ ≤ 12 := by omega
  have hU0 : 15 ≤ #U0 := by simpa [U0, S0] using hsize (0 : Fin 7)
  have hU1 : 28 ≤ #U1 := by
    have heq := Finset.card_union_add_card_inter U0 S1
    have hi : #(U0 ∩ S1) ≤ 2 := by simpa [Finset.inter_comm] using hI1
    have hs : 15 ≤ #S1 := by simpa [S1] using hsize (1 : Fin 7)
    dsimp [U1]
    omega
  have hU2 : 39 ≤ #U2 := by
    have heq := Finset.card_union_add_card_inter U1 S2
    have hi : #(U1 ∩ S2) ≤ 4 := by simpa [Finset.inter_comm] using hI2
    have hs : 15 ≤ #S2 := by simpa [S2] using hsize (2 : Fin 7)
    dsimp [U2]
    omega
  have hU3 : 48 ≤ #U3 := by
    have heq := Finset.card_union_add_card_inter U2 S3
    have hi : #(U2 ∩ S3) ≤ 6 := by simpa [Finset.inter_comm] using hI3
    have hs : 15 ≤ #S3 := by simpa [S3] using hsize (3 : Fin 7)
    dsimp [U3]
    omega
  have hU4 : 55 ≤ #U4 := by
    have heq := Finset.card_union_add_card_inter U3 S4
    have hi : #(U3 ∩ S4) ≤ 8 := by simpa [Finset.inter_comm] using hI4
    have hs : 15 ≤ #S4 := by simpa [S4] using hsize (4 : Fin 7)
    dsimp [U4]
    omega
  have hU5 : 60 ≤ #U5 := by
    have heq := Finset.card_union_add_card_inter U4 S5
    have hi : #(U4 ∩ S5) ≤ 10 := by simpa [Finset.inter_comm] using hI5
    have hs : 15 ≤ #S5 := by simpa [S5] using hsize (5 : Fin 7)
    dsimp [U5]
    omega
  have hU6 : 63 ≤ #U6 := by
    have heq := Finset.card_union_add_card_inter U5 S6
    have hi : #(U5 ∩ S6) ≤ 12 := by simpa [Finset.inter_comm] using hI6
    have hs : 15 ≤ #S6 := by simpa [S6] using hsize (6 : Fin 7)
    dsimp [U6]
    omega
  have hle : #U6 ≤ Fintype.card V := Finset.card_le_univ U6
  omega

/-- Structural endpoint of Stage A: in any hypothetical order-61
four-colouring there is a colour `delta` and a pair `u,v` with a common
`delta`-neighbourhood of order at least three; both endpoints have
`delta`-degree at least 15; their own edge is not `delta`; and its colour has
degree at least 14 at one endpoint. -/
theorem exists_attaching_pair_at_61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ delta : FourColor, ∃ u v : V,
      u ≠ v ∧ c u v ≠ delta ∧
      15 ≤ colorDegree c delta u ∧
      15 ≤ colorDegree c delta v ∧
      3 ≤ #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ∧
      (14 ≤ colorDegree c (c u v) u ∨
        14 ≤ colorDegree c (c u v) v) := by
  obtain ⟨delta, f, hlarge, hnonbad⟩ :=
    exists_largeColor_seven_pairwise_nonbad_at_61 hcard c hc
  let S : Fin 7 → Finset V := fun i ↦ colorNeighborhood c delta (f i)
  have hsize : ∀ i, 15 ≤ #(S i) := by
    intro i
    exact hlarge i
  obtain ⟨i, j, hij, hinter⟩ :=
    seven_large_finsets_overlap_three (by omega) S hsize
  have hinter' :
      3 ≤ #(colorNeighborhood c delta (f i) ∩
        colorNeighborhood c delta (f j)) := by
    simpa [S] using hinter
  have huv : f i ≠ f j := f.injective.ne hij
  have hnotdelta : c (f i) (f j) ≠ delta := by
    intro hedge
    have hnonempty :
        (colorNeighborhood c delta (f i) ∩
          colorNeighborhood c delta (f j)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨w, hw⟩ := hnonempty
    obtain ⟨hwi, hwj⟩ := Finset.mem_inter.mp hw
    have hwi' := (mem_colorNeighborhood c delta (f i) w).1 hwi
    have hwj' := (mem_colorNeighborhood c delta (f j) w).1 hwj
    apply hc (f i) (f j) w
    · exact ⟨huv, hwi'.1.symm, hwj'.1.symm⟩
    · exact ⟨hedge.trans hwi'.2.symm, hwi'.2.trans hwj'.2.symm⟩
  have hlargeEdge :
      14 ≤ colorDegree c (c (f i) (f j)) (f i) ∨
        14 ≤ colorDegree c (c (f i) (f j)) (f j) := by
    have hnb := hnonbad hij
    change ¬(f i ≠ f j ∧
      colorDegree c (c (f i) (f j)) (f i) ≤ 13 ∧
      colorDegree c (c (f i) (f j)) (f j) ≤ 13) at hnb
    by_cases hi : 14 ≤ colorDegree c (c (f i) (f j)) (f i)
    · exact Or.inl hi
    · right
      by_contra hj
      apply hnb
      exact ⟨huv, by omega, by omega⟩
  refine ⟨delta, f i, f j, huv, hnotdelta, hlarge i, hlarge j, ?_, hlargeEdge⟩
  exact hinter'

/-! ## The upper attaching-intersection bound -/

/-- An intersection of two differently coloured neighbourhoods is internally
two-coloured by the other two colours, hence has order at most five. -/
theorem two_neighborhood_inter_card_le_five_of_four
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (p q r s : C) (hexhaust : ∀ z : C, z = p ∨ z = q ∨ z = r ∨ z = s)
    (x y : V) :
    #(colorNeighborhood c p x ∩ colorNeighborhood c q y) ≤ 5 := by
  apply twoColorFinset_card_le_five c hc (p := r) (q := s)
      (colorNeighborhood c p x ∩ colorNeighborhood c q y)
  intro a ha b hb hab
  obtain ⟨hax, hay⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbx, hby⟩ := Finset.mem_inter.mp hb
  have hnotp := neighborhood_avoids_own_color c hc hax hbx hab
  have hnotq := neighborhood_avoids_own_color c hc hay hby hab
  rcases hexhaust (c a b) with hp | hq | hr | hs
  · exact (hnotp hp).elim
  · exact (hnotq hq).elim
  · exact Or.inl hr
  · exact Or.inr hs

/-- Two distinct concrete four-colours can be completed by two colours that
exhaust the colour type. -/
theorem fourColor_completion (delta gamma : FourColor) (hne : delta ≠ gamma) :
    ∃ alpha beta : FourColor,
      ∀ z : FourColor,
        z = delta ∨ z = gamma ∨ z = alpha ∨ z = beta := by
  classical
  let R : Finset FourColor :=
    ((Finset.univ : Finset FourColor).erase delta).erase gamma
  have hRcard : #R = 2 := by
    simp [R, hne.symm]
  obtain ⟨alpha, beta, hab, hR⟩ := Finset.card_eq_two.mp hRcard
  refine ⟨alpha, beta, ?_⟩
  intro z
  by_cases hd : z = delta
  · exact Or.inl hd
  by_cases hg : z = gamma
  · exact Or.inr (Or.inl hg)
  have hzR : z ∈ R := by simp [R, hd, hg]
  rw [hR] at hzR
  rcases Finset.mem_insert.mp hzR with ha | hb
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hb)))

/-- The high edge-colour neighbourhood is covered by the root, two parts of
order at most five, and the `delta` cross-part.  This records both the sharp
degree inequality and its order-three consequence. -/
theorem edgeColor_delta_cross_bounds_of_four
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (delta gamma alpha beta : C)
    (hexhaust : ∀ z : C,
      z = delta ∨ z = gamma ∨ z = alpha ∨ z = beta)
    {u v : V} (huv : u ≠ v) (hedge : c u v = gamma)
    (hdegree : 14 ≤ colorDegree c gamma u) :
    3 ≤ #(colorNeighborhood c gamma u ∩ colorNeighborhood c delta v) ∧
      colorDegree c gamma u ≤
        #(colorNeighborhood c gamma u ∩ colorNeighborhood c delta v) + 11 := by
  let A := colorNeighborhood c gamma u ∩ colorNeighborhood c alpha v
  let B := colorNeighborhood c gamma u ∩ colorNeighborhood c beta v
  let D := colorNeighborhood c gamma u ∩ colorNeighborhood c delta v
  let N := colorNeighborhood c gamma u
  have hA : #A ≤ 5 := by
    apply two_neighborhood_inter_card_le_five_of_four c hc
      gamma alpha delta beta
    intro z
    rcases hexhaust z with hd | hg | ha | hb
    · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inl hg
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr hb))
  have hB : #B ≤ 5 := by
    apply two_neighborhood_inter_card_le_five_of_four c hc
      gamma beta delta alpha
    intro z
    rcases hexhaust z with hd | hg | ha | hb
    · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inl hg
    · exact Or.inr (Or.inr (Or.inr ha))
    · exact Or.inr (Or.inl hb)
  let U : Finset V := ((({v} : Finset V) ∪ A) ∪ B) ∪ D
  have hsubset : N ⊆ U := by
    intro w hw
    by_cases hwv : w = v
    · simp [U, hwv]
    have hwN := (mem_colorNeighborhood c gamma u w).1 (by simpa [N] using hw)
    rcases hexhaust (c v w) with hd | hg | ha | hb
    · simp [U, A, B, D, N, hw, hwv, hd]
    · exfalso
      apply hc u v w
      · exact ⟨huv, hwN.1.symm, fun h ↦ hwv h.symm⟩
      · exact ⟨hedge.trans hwN.2.symm, hwN.2.trans hg.symm⟩
    · simp [U, A, B, D, N, hw, hwv, ha]
    · simp [U, A, B, D, N, hw, hwv, hb]
  have h1 := Finset.card_union_le ({v} : Finset V) A
  have h2 := Finset.card_union_le (({v} : Finset V) ∪ A) B
  have h3 := Finset.card_union_le ((({v} : Finset V) ∪ A) ∪ B) D
  have hU : #U ≤ 1 + #A + #B + #D := by
    calc
      #U ≤ #((({v} : Finset V) ∪ A) ∪ B) + #D := by
        simpa [U] using h3
      _ ≤ (#(({v} : Finset V) ∪ A) + #B) + #D :=
        Nat.add_le_add_right h2 #D
      _ ≤ ((#({v} : Finset V) + #A) + #B) + #D :=
        Nat.add_le_add_right (Nat.add_le_add_right h1 #B) #D
      _ = 1 + #A + #B + #D := by simp [Nat.add_assoc]
  have hN : #N ≤ #U := Finset.card_le_card hsubset
  have hdegree' : 14 ≤ #N := by simpa [N, colorDegree] using hdegree
  have hdegreeEq : colorDegree c gamma u = #N := by simp [N, colorDegree]
  change 3 ≤ #D ∧ colorDegree c gamma u ≤ #D + 11
  constructor <;> omega

/-- If `uv` has colour `gamma` and the `gamma`-degree at `u` is at least
14, at least three `gamma`-neighbours of `u` are `delta`-neighbours of `v`. -/
theorem edgeColor_delta_cross_ge_three_of_four
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (delta gamma alpha beta : C)
    (hexhaust : ∀ z : C,
      z = delta ∨ z = gamma ∨ z = alpha ∨ z = beta)
    {u v : V} (huv : u ≠ v) (hedge : c u v = gamma)
    (hdegree : 14 ≤ colorDegree c gamma u) :
    3 ≤ #(colorNeighborhood c gamma u ∩ colorNeighborhood c delta v) :=
  (edgeColor_delta_cross_bounds_of_four c hc delta gamma alpha beta
    hexhaust huv hedge hdegree).1

/-- The partition and disjointness arguments retain a sharper inequality
than the order-13 corollary: edge-colour degree plus attaching order is at
most the opposite `delta`-degree plus eleven. -/
theorem attaching_degree_intersection_inequality_of_four
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (delta gamma alpha beta : C)
    (hexhaust : ∀ z : C,
      z = delta ∨ z = gamma ∨ z = alpha ∨ z = beta)
    {u v : V} (huv : u ≠ v) (hedge : c u v = gamma)
    (hgammaDelta : gamma ≠ delta)
    (hgammaDegree : 14 ≤ colorDegree c gamma u) :
    colorDegree c gamma u +
        #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤
      colorDegree c delta v + 11 := by
  let D := colorNeighborhood c gamma u ∩ colorNeighborhood c delta v
  let I := colorNeighborhood c delta u ∩ colorNeighborhood c delta v
  let Nv := colorNeighborhood c delta v
  have hpartition : colorDegree c gamma u ≤ #D + 11 := by
    simpa [D] using (edgeColor_delta_cross_bounds_of_four
      c hc delta gamma alpha beta hexhaust huv hedge hgammaDegree).2
  have hdisjoint : Disjoint D I := by
    rw [Finset.disjoint_left]
    intro w hwD hwI
    obtain ⟨hwGamma, _⟩ := Finset.mem_inter.mp hwD
    obtain ⟨hwDelta, _⟩ := Finset.mem_inter.mp hwI
    have hGamma := (mem_colorNeighborhood c gamma u w).1 hwGamma
    have hDelta := (mem_colorNeighborhood c delta u w).1 hwDelta
    exact hgammaDelta (hGamma.2.symm.trans hDelta.2)
  have hDsub : D ⊆ Nv := fun _ hw ↦ (Finset.mem_inter.mp hw).2
  have hIsub : I ⊆ Nv := fun _ hw ↦ (Finset.mem_inter.mp hw).2
  have hunionSub : D ∪ I ⊆ Nv := Finset.union_subset hDsub hIsub
  have hunionCard : #(D ∪ I) = #D + #I :=
    Finset.card_union_of_disjoint hdisjoint
  have hinside : #(D ∪ I) ≤ #Nv := Finset.card_le_card hunionSub
  have hNvEq : #Nv = colorDegree c delta v := by simp [Nv, colorDegree]
  change colorDegree c gamma u + #I ≤ colorDegree c delta v + 11
  omega

/-- The three-vertex cross-part is disjoint from the attaching intersection
inside a `delta`-neighbourhood of order at most 16, forcing attaching order
at most 13. -/
theorem attaching_intersection_le_thirteen_of_four
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (hc : NoMonochromaticTriangle c)
    (delta gamma alpha beta : C)
    (hexhaust : ∀ z : C,
      z = delta ∨ z = gamma ∨ z = alpha ∨ z = beta)
    {u v : V} (huv : u ≠ v) (hedge : c u v = gamma)
    (hgammaDelta : gamma ≠ delta)
    (hgammaDegree : 14 ≤ colorDegree c gamma u)
    (hdeltaDegree : colorDegree c delta v ≤ 16) :
    #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤ 13 := by
  let D := colorNeighborhood c gamma u ∩ colorNeighborhood c delta v
  let I := colorNeighborhood c delta u ∩ colorNeighborhood c delta v
  let Nv := colorNeighborhood c delta v
  have hcross : 3 ≤ #D := by
    simpa [D] using edgeColor_delta_cross_ge_three_of_four
      c hc delta gamma alpha beta hexhaust huv hedge hgammaDegree
  have hdisjoint : Disjoint D I := by
    rw [Finset.disjoint_left]
    intro w hwD hwI
    obtain ⟨hwGamma, _⟩ := Finset.mem_inter.mp hwD
    obtain ⟨hwDelta, _⟩ := Finset.mem_inter.mp hwI
    have hGamma := (mem_colorNeighborhood c gamma u w).1 hwGamma
    have hDelta := (mem_colorNeighborhood c delta u w).1 hwDelta
    exact hgammaDelta (hGamma.2.symm.trans hDelta.2)
  have hDsub : D ⊆ Nv := by
    intro w hw
    exact (Finset.mem_inter.mp hw).2
  have hIsub : I ⊆ Nv := by
    intro w hw
    exact (Finset.mem_inter.mp hw).2
  have hunionSub : D ∪ I ⊆ Nv := Finset.union_subset hDsub hIsub
  have hunionCard : #(D ∪ I) = #D + #I :=
    Finset.card_union_of_disjoint hdisjoint
  have hinside : #(D ∪ I) ≤ #Nv := Finset.card_le_card hunionSub
  have hNv : #Nv ≤ 16 := by
    simpa [Nv, colorDegree] using hdeltaDegree
  change #I ≤ 13
  omega

/-- Concrete four-colour wrapper around the preceding partition theorem. -/
theorem fourColor_attaching_intersection_le_thirteen_oriented
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta gamma : FourColor) {u v : V}
    (huv : u ≠ v) (hedge : c u v = gamma)
    (hgammaDelta : gamma ≠ delta)
    (hgammaDegree : 14 ≤ colorDegree c gamma u)
    (hdeltaDegree : colorDegree c delta v ≤ 16) :
    #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤ 13 := by
  obtain ⟨alpha, beta, hexhaust⟩ :=
    fourColor_completion delta gamma hgammaDelta.symm
  exact attaching_intersection_le_thirteen_of_four
    c hc delta gamma alpha beta hexhaust huv hedge hgammaDelta
      hgammaDegree hdeltaDegree

/-- Concrete four-colour form of the retained attaching-degree inequality. -/
theorem fourColor_attaching_degree_intersection_inequality_oriented
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta gamma : FourColor) {u v : V}
    (huv : u ≠ v) (hedge : c u v = gamma)
    (hgammaDelta : gamma ≠ delta)
    (hgammaDegree : 14 ≤ colorDegree c gamma u) :
    colorDegree c gamma u +
        #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤
      colorDegree c delta v + 11 := by
  obtain ⟨alpha, beta, hexhaust⟩ :=
    fourColor_completion delta gamma hgammaDelta.symm
  exact attaching_degree_intersection_inequality_of_four
    c hc delta gamma alpha beta hexhaust huv hedge hgammaDelta hgammaDegree

/-- Full catalogue-free Stage A endpoint at order 61.  The two selected
`delta`-neighbourhoods have orders in `{15,16}` and their intersection has
order in the exact structural range `3,...,13`. -/
theorem existsAttaching61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ delta : FourColor, ∃ u v : V,
      u ≠ v ∧ c u v ≠ delta ∧
      15 ≤ colorDegree c delta u ∧ colorDegree c delta u ≤ 16 ∧
      15 ≤ colorDegree c delta v ∧ colorDegree c delta v ≤ 16 ∧
      3 ≤ #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ∧
      #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤ 13 := by
  obtain ⟨delta, u, v, huv, hnotdelta, hduLower, hdvLower,
      hinterLower, hhigh⟩ := exists_attaching_pair_at_61 hcard c hc
  have hduUpper := fourColor_colorDegree_le_sixteen c hc delta u
  have hdvUpper := fourColor_colorDegree_le_sixteen c hc delta v
  have hinterUpper :
      #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤ 13 := by
    rcases hhigh with huHigh | hvHigh
    · exact fourColor_attaching_intersection_le_thirteen_oriented
        c hc delta (c u v) huv rfl hnotdelta huHigh hdvUpper
    · have hedgeSymm : c v u = c u v := (c.color_symm u v).symm
      have hnotdeltaSymm : c v u ≠ delta := by
        intro h
        exact hnotdelta (hedgeSymm.symm.trans h)
      have hvHighSymm : 14 ≤ colorDegree c (c v u) v := by
        simpa [hedgeSymm] using hvHigh
      have hswapped := fourColor_attaching_intersection_le_thirteen_oriented
        c hc delta (c v u) huv.symm rfl hnotdeltaSymm hvHighSymm hduUpper
      simpa [Finset.inter_comm] using hswapped
  exact ⟨delta, u, v, huv, hnotdelta, hduLower, hduUpper,
    hdvLower, hdvUpper, hinterLower, hinterUpper⟩

/-- Strengthened oriented Stage A endpoint.  The pair is ordered so that its
edge colour `gamma = c u v` has degree at least 14 at `u`.  Besides the
range theorem, this retains the sharp partition inequality

`d_gamma(u) + k <= d_delta(v) + 11`,

and hence `k + 3 <= d_delta(v)`. -/
theorem existsAttaching61_oriented
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ delta : FourColor, ∃ u v : V,
      u ≠ v ∧ c u v ≠ delta ∧
      14 ≤ colorDegree c (c u v) u ∧
      15 ≤ colorDegree c delta u ∧ colorDegree c delta u ≤ 16 ∧
      15 ≤ colorDegree c delta v ∧ colorDegree c delta v ≤ 16 ∧
      3 ≤ #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ∧
      #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤ 13 ∧
      colorDegree c (c u v) u +
          #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤
        colorDegree c delta v + 11 ∧
      #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) + 3 ≤
        colorDegree c delta v := by
  obtain ⟨delta, u, v, huv, hnotdelta, hduLower, hdvLower,
      hinterLower, hhigh⟩ := exists_attaching_pair_at_61 hcard c hc
  have hduUpper := fourColor_colorDegree_le_sixteen c hc delta u
  have hdvUpper := fourColor_colorDegree_le_sixteen c hc delta v
  rcases hhigh with huHigh | hvHigh
  · have hineq := fourColor_attaching_degree_intersection_inequality_oriented
      c hc delta (c u v) huv rfl hnotdelta huHigh
    have hplus :
        #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) + 3 ≤
          colorDegree c delta v := by
      omega
    have hupper :
        #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤ 13 := by
      omega
    exact ⟨delta, u, v, huv, hnotdelta, huHigh,
      hduLower, hduUpper, hdvLower, hdvUpper,
      hinterLower, hupper, hineq, hplus⟩
  · have hedgeSymm : c v u = c u v := (c.color_symm u v).symm
    have hnotdeltaSymm : c v u ≠ delta := by
      intro h
      exact hnotdelta (hedgeSymm.symm.trans h)
    have hvHighSymm : 14 ≤ colorDegree c (c v u) v := by
      simpa [hedgeSymm] using hvHigh
    have hinterLowerSymm :
        3 ≤ #(colorNeighborhood c delta v ∩ colorNeighborhood c delta u) := by
      simpa [Finset.inter_comm] using hinterLower
    have hineq := fourColor_attaching_degree_intersection_inequality_oriented
      c hc delta (c v u) huv.symm rfl hnotdeltaSymm hvHighSymm
    have hplus :
        #(colorNeighborhood c delta v ∩ colorNeighborhood c delta u) + 3 ≤
          colorDegree c delta u := by
      omega
    have hupper :
        #(colorNeighborhood c delta v ∩ colorNeighborhood c delta u) ≤ 13 := by
      omega
    exact ⟨delta, v, u, huv.symm, hnotdeltaSymm, hvHighSymm,
      hdvLower, hdvUpper, hduLower, hduUpper,
      hinterLowerSymm, hupper, hineq, hplus⟩

end R4333

#print axioms R4333.forcesTwoCard_6_3_3
#print axioms R4333.forcesTwoCard_28_3_7
#print axioms R4333.triangleFree_exists_independent7
#print axioms R4333.neighborhood_avoids_own_color
#print axioms R4333.badPairGraph_cliqueFree_three
#print axioms R4333.threeColorFinset_card_le_sixteen
#print axioms R4333.fourColor_colorDegree_le_sixteen
#print axioms R4333.fourColor_largeIncidences_ge_122
#print axioms R4333.exists_largeColor_seven_pairwise_nonbad_at_61
#print axioms R4333.seven_large_finsets_overlap_three
#print axioms R4333.exists_attaching_pair_at_61
#print axioms R4333.two_neighborhood_inter_card_le_five_of_four
#print axioms R4333.edgeColor_delta_cross_ge_three_of_four
#print axioms R4333.edgeColor_delta_cross_bounds_of_four
#print axioms R4333.attaching_degree_intersection_inequality_of_four
#print axioms R4333.attaching_intersection_le_thirteen_of_four
#print axioms R4333.existsAttaching61
#print axioms R4333.existsAttaching61_oriented
