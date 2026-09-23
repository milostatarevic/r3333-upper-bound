import PricingC.BinarySupports
import PricingC.GSmallFamilies

namespace PricingC.GParity
open Finset Matrix PricingG

structure ResidualPentagons {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (k : Nat) where
  rows : Finset V
  family : Finset (Finset V)
  card_rows : rows.card = k
  card_family : family.card = k
  subsets : ∀ S ∈ family, S ⊆ rows
  sizes : ∀ S ∈ family, S.card = 5
  columns_even : ∀ S ∈ family, ∀ T ∈ family, S ≠ T → Even (S ∩ T).card
  rows_even : ∀ a b, a ≠ b → Even (family.filter fun S => a ∈ S ∧ b ∈ S).card
  rows_odd : ∀ a ∈ rows, Odd (family.filter fun S => a ∈ S).card
  cycles : ∀ S ∈ family, InducedDegreeTwo K S

/-- Delete every unit column and its occupied physical row. Orthogonality
proves that every remaining support is disjoint from all deleted rows. -/
theorem extract_residual_pentagons {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (P : Matrix V V (ZMod 2))
    (hcols : Pᵀ * P = 1) (hrows : P * Pᵀ = 1) (D : Finset V)
    (hunit : ∀ j, j ∉ D → ∃ a, columnSupport P j = {a})
    (hpent : ∀ j ∈ D, (columnSupport P j).card = 5 ∧ InducedDegreeTwo K (columnSupport P j)) :
    Nonempty (ResidualPentagons K D.card) := by
  classical
  have hex : ∀ j : ↥Dᶜ, ∃ a, columnSupport P j.val = {a} :=
    fun j => hunit j.val (mem_compl.mp j.property)
  choose center hcenter using hex
  have hcinj : Function.Injective center := by
    intro i j hij
    apply Subtype.ext
    apply binary_columns_injective P hcols
    rw [hcenter i,hcenter j,hij]
  let U := (univ : Finset ↥Dᶜ).image center
  let R := Uᶜ
  let F := D.image (columnSupport P)
  have hU : U.card = Dᶜ.card := by
    rw [card_image_of_injective _ hcinj,card_univ,Fintype.card_coe]
  have hR : R.card = D.card := by
    change Uᶜ.card = D.card
    rw [card_compl,hU,card_compl]
    have hle : D.card ≤ Fintype.card V := card_le_univ D
    omega
  have hF : F.card = D.card := card_image_of_injective _ (binary_columns_injective P hcols)
  have hsubcol : ∀ j ∈ D, columnSupport P j ⊆ R := by
    intro j hj x hx
    apply mem_compl.mpr
    intro hxu
    obtain ⟨a,_,rfl⟩ := mem_image.mp hxu
    have hja : j ≠ a.val := by intro he; exact (mem_compl.mp a.property) (he ▸ hj)
    have hp := binary_columns_even P hcols j a.val hja
    rw [hcenter a] at hp
    have heq : columnSupport P j ∩ {center a} = {center a} := by ext z; simp [hx]
    rw [heq,card_singleton] at hp
    norm_num at hp
  have hsub : ∀ S ∈ F, S ⊆ R := by
    intro S hS
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hS
    exact hsubcol j hj
  have hzero : ∀ x ∈ R, ∀ j, j ∉ D → ¬ P x j = 1 := by
    intro x hx j hj hp
    let a : ↥Dᶜ := ⟨j,mem_compl.mpr hj⟩
    have hxcol : x ∈ columnSupport P j := mem_filter.mpr ⟨mem_univ _,hp⟩
    have he : x = center a := by rw [hcenter a] at hxcol; exact mem_singleton.mp hxcol
    exact (mem_compl.mp hx) (mem_image.mpr ⟨a,mem_univ _,he.symm⟩)
  have count_image (Q : Finset V → Prop) [DecidablePred Q] :
      (F.filter Q).card = (D.filter fun j => Q (columnSupport P j)).card := by
    rw [show F = D.image (columnSupport P) from rfl,filter_image,
      card_image_of_injective _ (binary_columns_injective P hcols)]
  have hroweq (x : V) (hx : x ∈ R) :
      (F.filter fun S => x ∈ S).card = (univ.filter fun j => P x j = 1).card := by
    rw [count_image]
    congr 1
    ext j
    simp only [mem_filter,columnSupport,mem_univ,true_and]
    exact ⟨fun h => h.2,fun h => ⟨by by_contra hn; exact hzero x hx j hn h,h⟩⟩
  have hrowpair (x y : V) (hx : x ∈ R) :
      (F.filter fun S => x ∈ S ∧ y ∈ S).card =
        (univ.filter fun j => P x j = 1 ∧ P y j = 1).card := by
    rw [count_image]
    congr 1
    ext j
    simp only [mem_filter,columnSupport,mem_univ,true_and]
    exact ⟨fun h => h.2,fun h => ⟨by by_contra hn; exact hzero x hx j hn h.1,h⟩⟩
  refine ⟨⟨R,F,hR,hF,hsub,?_,?_,?_,?_,?_⟩⟩
  · intro S hS
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hS
    exact (hpent j hj).1
  · intro S hS T hT hST
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hT
    exact binary_columns_even P hcols i j (fun h => hST (congrArg (columnSupport P) h))
  · intro x y hxy
    by_cases hx : x ∈ R
    · rw [hrowpair x y hx]
      exact binary_rows_even P hrows x y hxy
    · have heq : F.filter (fun S => x ∈ S ∧ y ∈ S) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro S hS
        exact hx (hsub S (mem_filter.mp hS).1 (mem_filter.mp hS).2.1)
      rw [heq,card_empty]
      exact ⟨0,rfl⟩
  · intro x hx
    rw [hroweq x hx]
    exact binary_row_odd P hrows x
  · intro S hS
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hS
    exact (hpent j hj).2

#print axioms extract_residual_pentagons
end PricingC.GParity
