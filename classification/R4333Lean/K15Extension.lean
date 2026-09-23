import R4333Lean.ThreeColorCatalogue

/-!
# The canonical extension of a critical three-colouring on fifteen vertices

The only finite input needed here is `DeficientEdgeFree`: endpoints whose
unique degree-four colour is `q` are never joined in colour `q`.  Everything
else in this file is ordinary kernel-checked combinatorics.
-/

namespace R4333

private theorem fin3_cases_k15 (q : ThreeColor) :
    q = 0 ∨ q = 1 ∨ q = 2 := by
  fin_cases q <;> simp

/-- Every colour degree in a good three-colouring is at most five. -/
theorem threeColor_degree_le_five
    {n : Nat} (c : EdgeColoring (Fin n) ThreeColor)
    (hc : NoMonochromaticTriangle c) (q : ThreeColor) (v : Fin n) :
    colorDegree c q v ≤ 5 := by
  fin_cases q
  · apply twoColorFinset_card_le_five c hc
      (p := (1 : Fin 3)) (q := (2 : Fin 3))
      (colorNeighborhood c (0 : Fin 3) v)
    intro x hx y hy hxy
    have hnot := neighborhood_avoids_own_color c hc hx hy hxy
    rcases fin3_cases_k15 (c x y) with h | h | h <;> simp_all
  · apply twoColorFinset_card_le_five c hc
      (p := (0 : Fin 3)) (q := (2 : Fin 3))
      (colorNeighborhood c (1 : Fin 3) v)
    intro x hx y hy hxy
    have hnot := neighborhood_avoids_own_color c hc hx hy hxy
    rcases fin3_cases_k15 (c x y) with h | h | h <;> simp_all
  · apply twoColorFinset_card_le_five c hc
      (p := (0 : Fin 3)) (q := (1 : Fin 3))
      (colorNeighborhood c (2 : Fin 3) v)
    intro x hx y hy hxy
    have hnot := neighborhood_avoids_own_color c hc hx hy hxy
    rcases fin3_cases_k15 (c x y) with h | h | h <;> simp_all

/-- At order fifteen every colour degree is either four or five. -/
theorem threeColor_degree_four_or_five_at_15
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (q : ThreeColor) (v : Fin 15) :
    colorDegree c q v = 4 ∨ colorDegree c q v = 5 := by
  have hle : ∀ r : ThreeColor, colorDegree c r v ≤ 5 :=
    fun r => threeColor_degree_le_five c hc r v
  have hsum := sum_colorDegree_eq_card_sub_one c v
  have hsum' :
      colorDegree c (0 : Fin 3) v +
        (colorDegree c (1 : Fin 3) v + colorDegree c (2 : Fin 3) v) = 14 := by
    simpa [Fin.sum_univ_succ] using hsum
  rcases fin3_cases_k15 q with rfl | rfl | rfl <;>
    specialize hle (0 : Fin 3) <;>
    have h1 := threeColor_degree_le_five c hc (1 : Fin 3) v <;>
    have h2 := threeColor_degree_le_five c hc (2 : Fin 3) v <;>
    omega

/-- Every vertex has a unique degree-four colour at order fifteen. -/
theorem existsUnique_deficientColor_at_15
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (v : Fin 15) :
    ∃! q : ThreeColor, colorDegree c q v = 4 := by
  have hsum := sum_colorDegree_eq_card_sub_one c v
  have hsum' :
      colorDegree c (0 : Fin 3) v +
        (colorDegree c (1 : Fin 3) v + colorDegree c (2 : Fin 3) v) = 14 := by
    simpa [Fin.sum_univ_succ] using hsum
  have h0 := threeColor_degree_four_or_five_at_15 c hc (0 : Fin 3) v
  have h1 := threeColor_degree_four_or_five_at_15 c hc (1 : Fin 3) v
  have h2 := threeColor_degree_four_or_five_at_15 c hc (2 : Fin 3) v
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2
  all_goals
    first
    | refine ⟨0, h0, ?_⟩
    | refine ⟨1, h1, ?_⟩
    | refine ⟨2, h2, ?_⟩
    | omega
  all_goals
    intro q hq
    fin_cases q <;> simp_all

/-- The unique degree-four colour at a vertex of a good `K15`. -/
noncomputable def deficientColor15
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (v : Fin 15) : ThreeColor :=
  Classical.choose (existsUnique_deficientColor_at_15 c hc v)

theorem deficientColor15_degree
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (v : Fin 15) :
    colorDegree c (deficientColor15 c hc v) v = 4 :=
  (Classical.choose_spec (existsUnique_deficientColor_at_15 c hc v)).1

theorem degree_eq_five_of_ne_deficientColor15
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (v : Fin 15) (q : ThreeColor)
    (hne : q ≠ deficientColor15 c hc v) :
    colorDegree c q v = 5 := by
  rcases threeColor_degree_four_or_five_at_15 c hc q v with hfour | hfive
  · have hunique :=
      (Classical.choose_spec (existsUnique_deficientColor_at_15 c hc v)).2 q hfour
    exact (hne hunique).elim
  · exact hfive

/-- Add one last vertex, joining it to old vertex `v` in colour `d v`.
The diagonal value at the new vertex is deliberately arbitrary. -/
def extendByLast
    {n : Nat} {C : Type*} (c : EdgeColoring (Fin n) C)
    (d : Fin n → C) (diagonal : C) : EdgeColoring (Fin (n + 1)) C where
  color u v :=
    Fin.lastCases
      (Fin.lastCases diagonal (fun j => d j) v)
      (fun i => Fin.lastCases (d i) (fun j => c i j) v)
      u
  color_symm u v := by
    induction u using Fin.lastCases with
    | last =>
        induction v using Fin.lastCases <;> simp
    | cast i =>
        induction v using Fin.lastCases with
        | last => simp
        | cast j => simpa using c.color_symm i j

@[simp]
theorem extendByLast_old_old
    {n : Nat} {C : Type*} (c : EdgeColoring (Fin n) C)
    (d : Fin n → C) (diagonal : C) (i j : Fin n) :
    extendByLast c d diagonal i.castSucc j.castSucc = c i j := by
  simp [extendByLast]

@[simp]
theorem extendByLast_last_old
    {n : Nat} {C : Type*} (c : EdgeColoring (Fin n) C)
    (d : Fin n → C) (diagonal : C) (i : Fin n) :
    extendByLast c d diagonal (Fin.last n) i.castSucc = d i := by
  simp [extendByLast]

@[simp]
theorem extendByLast_old_last
    {n : Nat} {C : Type*} (c : EdgeColoring (Fin n) C)
    (d : Fin n → C) (diagonal : C) (i : Fin n) :
    extendByLast c d diagonal i.castSucc (Fin.last n) = d i := by
  simp [extendByLast]

/-- Adding the last vertex changes an old vertex's degree in colour `q` by
exactly one precisely when its new incident edge has colour `q`. -/
theorem colorDegree_extendByLast_old
    {n : Nat} {C : Type*} [Fintype C] [DecidableEq C]
    (c : EdgeColoring (Fin n) C) (d : Fin n → C) (diagonal q : C)
    (i : Fin n) :
    colorDegree (extendByLast c d diagonal) q i.castSucc =
      colorDegree c q i + if d i = q then 1 else 0 := by
  classical
  simp only [colorDegree, colorNeighborhood, Fin.univ_castSuccEmb]
  rw [Finset.filter_cons]
  have hold :
      {x ∈ Finset.map Fin.castSuccEmb (Finset.univ : Finset (Fin n)) |
          x ≠ i.castSucc ∧ extendByLast c d diagonal i.castSucc x = q} =
        Finset.map Fin.castSuccEmb
          {x ∈ (Finset.univ : Finset (Fin n)) | x ≠ i ∧ c i x = q} := by
    ext x
    induction x using Fin.lastCases with
    | last => simp
    | cast y => simp [extendByLast]
  have hne : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  by_cases h : d i = q
  · simp [h, hne, hold]
  · simp [h, hne, hold]

/-- Exact finite statement needed to make the deficient-colour extension
triangle-free. -/
def DeficientEdgeFree
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) : Prop :=
  ∀ ⦃u v : Fin 15⦄, u ≠ v →
    deficientColor15 c hc u = deficientColor15 c hc v →
    c u v ≠ deficientColor15 c hc u

/-- A last-vertex extension is triangle-free whenever equal attachment
colours do not occur on their corresponding old edge. -/
theorem noMono_extendByLast
    {n : Nat} {C : Type*} (c : EdgeColoring (Fin n) C)
    (hc : NoMonochromaticTriangle c) (d : Fin n → C) (diagonal : C)
    (hfree : ∀ ⦃u v : Fin n⦄, u ≠ v → d u = d v → c u v ≠ d u) :
    NoMonochromaticTriangle (extendByLast c d diagonal) := by
  intro x y z hdistinct hmono
  induction x using Fin.lastCases with
  | last =>
      induction y using Fin.lastCases with
      | last => exact hdistinct.1 rfl
      | cast i =>
          induction z using Fin.lastCases with
          | last => exact hdistinct.2.1 rfl
          | cast j =>
              have hij : i ≠ j := by
                intro h
                apply hdistinct.2.2
                simpa using h
              have hcolors : d i = d j ∧ d j = c i j := by
                simpa [HomogeneousTriangle] using hmono
              exact hfree hij hcolors.1
                (hcolors.2.symm.trans hcolors.1.symm)
  | cast i =>
      induction y using Fin.lastCases with
      | last =>
          induction z using Fin.lastCases with
          | last => exact hdistinct.2.2 rfl
          | cast j =>
              have hij : i ≠ j := by
                intro h
                apply hdistinct.2.1
                simpa using h
              have hcolors : d i = c i j ∧ c i j = d j := by
                simpa [HomogeneousTriangle] using hmono
              exact hfree hij (hcolors.1.trans hcolors.2) hcolors.1.symm
      | cast j =>
          induction z using Fin.lastCases with
          | last =>
              have hij : i ≠ j := by
                intro h
                apply hdistinct.1
                simpa using h
              have hcolors : c i j = d i ∧ d i = d j := by
                simpa [HomogeneousTriangle] using hmono
              exact hfree hij hcolors.2 hcolors.1
          | cast k =>
              apply hc i j k
              · constructor
                · intro h
                  apply hdistinct.1
                  simpa using h
                · constructor
                  · intro h
                    apply hdistinct.2.1
                    simpa using h
                  · intro h
                    apply hdistinct.2.2
                    simpa using h
              · simpa [HomogeneousTriangle] using hmono

/-- The canonical deficient-colour extension of a good `K15`. -/
noncomputable def extendCriticalK15
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) : EdgeColoring (Fin 16) ThreeColor :=
  extendByLast c (deficientColor15 c hc) 0

theorem extendCriticalK15_good
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c)
    (hfree : DeficientEdgeFree c hc) :
    NoMonochromaticTriangle (extendCriticalK15 c hc) := by
  apply noMono_extendByLast c hc (deficientColor15 c hc) 0
  exact hfree

/-- A good extension of a critical `K15` has no freedom in its attachment
colours: every old vertex must use its unique degree-four colour. -/
theorem attachment_eq_deficientColor15
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (d : Fin 15 → ThreeColor)
    (diagonal : ThreeColor)
    (hext : NoMonochromaticTriangle (extendByLast c d diagonal)) :
    d = deficientColor15 c hc := by
  funext v
  have hdeg := threeColor_degree_eq_five_at_16
    (extendByLast c d diagonal) hext (d v) v.castSucc
  rw [colorDegree_extendByLast_old] at hdeg
  simp at hdeg
  have hfour : colorDegree c (d v) v = 4 := by omega
  exact (Classical.choose_spec
    (existsUnique_deficientColor_at_15 c hc v)).2 (d v) hfour

/-- Consequently, any two good one-vertex extensions of the same labeled
critical `K15` agree on every non-diagonal edge. -/
theorem good_extensions_agree_off_diagonal
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c)
    (d₁ d₂ : Fin 15 → ThreeColor) (a₁ a₂ : ThreeColor)
    (h₁ : NoMonochromaticTriangle (extendByLast c d₁ a₁))
    (h₂ : NoMonochromaticTriangle (extendByLast c d₂ a₂))
    (u v : Fin 16) (huv : u ≠ v) :
    extendByLast c d₁ a₁ u v = extendByLast c d₂ a₂ u v := by
  have hd : d₁ = d₂ :=
    (attachment_eq_deficientColor15 c hc d₁ a₁ h₁).trans
      (attachment_eq_deficientColor15 c hc d₂ a₂ h₂).symm
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast j => rw [extendByLast_last_old, extendByLast_last_old, hd]
  | cast i =>
      induction v using Fin.lastCases with
      | last => rw [extendByLast_old_last, extendByLast_old_last, hd]
      | cast j => simp

#print axioms R4333.threeColor_degree_four_or_five_at_15
#print axioms R4333.existsUnique_deficientColor_at_15
#print axioms R4333.noMono_extendByLast
#print axioms R4333.extendCriticalK15_good
#print axioms R4333.attachment_eq_deficientColor15
#print axioms R4333.good_extensions_agree_off_diagonal

end R4333
