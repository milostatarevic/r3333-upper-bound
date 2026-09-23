import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Ramsey61
open Finset SimpleGraph
universe u

/-- A symmetric colouring of the unordered pairs of `V`.  Values on the
diagonal are irrelevant; all triangle predicates explicitly require three
distinct vertices. -/
@[ext]
structure EdgeColoring (V : Type*) (C : Type*) where
  color : V → V → C
  color_symm : ∀ u v, color u v = color v u

instance {V C : Type*} : CoeFun (EdgeColoring V C) (fun _ ↦ V → V → C) where
  coe c := c.color

/-- Three vertices are pairwise distinct. -/
def PairwiseDistinct {V : Type*} (x y z : V) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z

/-- The three edges on `x,y,z` have one common colour. -/
def HomogeneousTriangle {V C : Type*} (c : EdgeColoring V C) (x y z : V) : Prop :=
  c x y = c x z ∧ c x z = c y z

/-- A complete-graph edge colouring with no monochromatic triangle. -/
def NoMonochromaticTriangle {V C : Type*} (c : EdgeColoring V C) : Prop :=
  ∀ x y z, PairwiseDistinct x y z → ¬HomogeneousTriangle c x y z

/-- Our concrete four-element colour type. -/
abbrev FourColor := Bool × Bool

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


end Ramsey61
