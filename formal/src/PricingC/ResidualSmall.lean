import PricingC.BinaryResidual

namespace PricingC.GParity
open Finset PricingG

 theorem relative_complement_inter_card {V : Type*} [DecidableEq V]
    (R S T : Finset V) (hS : S ⊆ R) (hT : T ⊆ R) :
    ((R \ S) ∩ (R \ T)).card + S.card + T.card = R.card + (S ∩ T).card := by
  have heq : (R \ S) ∩ (R \ T) = R \ (S ∪ T) := by ext x; simp; tauto
  rw [heq]
  have h1 := card_sdiff_add_card_eq_card (union_subset hS hT)
  have h2 := card_union_add_card_inter S T
  omega

theorem relative_complement_inter_even {V : Type*} [DecidableEq V]
    (R S T : Finset V) (hS : S ⊆ R) (hT : T ⊆ R)
    (hR : Even R.card) (hSo : Odd S.card) (hTo : Odd T.card)
    (hST : Even (S ∩ T).card) : Even ((R \ S) ∩ (R \ T)).card := by
  have h := relative_complement_inter_card R S T hS hT
  simp only [Nat.even_iff] at hR hST ⊢
  simp only [Nat.odd_iff] at hSo hTo
  omega

theorem residual_not_eight {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (f : ResidualPentagons K 8) : False := by
  classical
  let R := f.rows
  let F := f.family
  let comp := fun S : Finset V => R \ S
  let H := F.image comp
  have hinj : Set.InjOn comp ↑F := by
    intro S hS T hT he
    have hS' := Finset.sdiff_sdiff_eq_self (f.subsets S hS)
    have hT' := Finset.sdiff_sdiff_eq_self (f.subsets T hT)
    change R \ (R \ S) = S at hS'
    change R \ (R \ T) = T at hT'
    rw [← hS', ← hT']
    exact congrArg (fun A => R \ A) he
  have card_filter_image (Q : Finset V → Prop) [DecidablePred Q] :
      (H.filter Q).card = (F.filter fun S => Q (comp S)).card := by
    rw [show H = F.image comp from rfl, filter_image]
    exact card_image_iff.mpr (fun _ hS _ hT h => hinj (mem_filter.mp hS).1 (mem_filter.mp hT).1 h)
  have hsize : H.card = 8 := by
    change (F.image comp).card = 8
    rw [card_image_iff.mpr hinj]
    exact f.card_family
  have hsub : ∀ S ∈ H, S ⊆ R := by
    intro S hS
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hS
    exact sdiff_subset
  apply no_eight_relative_pentagon_complements K R f.card_rows H hsize hsub
  · intro S hS
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hS
    change (R \ T).card = 3
    rw [card_sdiff_of_subset (f.subsets T hT),f.card_rows,f.sizes T hT]
  · intro S hS T hT hST
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hS
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hT
    have hAB : A ≠ B := fun h => hST (congrArg comp h)
    apply relative_complement_inter_even R A B (f.subsets A hA) (f.subsets B hB)
    · rw [f.card_rows]; decide
    · rw [f.sizes A hA]; decide
    · rw [f.sizes B hB]; decide
    · exact f.columns_even A hA B hB hAB
  · intro a b hab
    by_cases ha : a ∈ R
    · by_cases hb : b ∈ R
      · rw [card_filter_image]
        let Fa := F.filter fun S => a ∈ S
        let Fb := F.filter fun S => b ∈ S
        have heq : (F.filter fun S => a ∈ comp S ∧ b ∈ comp S) =
            (F \ Fa) ∩ (F \ Fb) := by
          ext S
          simp [Fa,Fb,comp,ha,hb]
          tauto
        rw [heq]
        apply relative_complement_inter_even F Fa Fb (filter_subset _ _) (filter_subset _ _)
        · rw [f.card_family]; decide
        · exact f.rows_odd a ha
        · exact f.rows_odd b hb
        · have heq' : Fa ∩ Fb = F.filter fun S => a ∈ S ∧ b ∈ S := by
            ext S; simp [Fa,Fb]; tauto
          rw [heq']
          exact f.rows_even a b hab
      · have hempty : (H.filter fun S => a ∈ S ∧ b ∈ S) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro S hS
          exact hb (hsub S (mem_filter.mp hS).1 (mem_filter.mp hS).2.2)
        rw [hempty,card_empty]; exact ⟨0,rfl⟩
    · have hempty : (H.filter fun S => a ∈ S ∧ b ∈ S) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro S hS
        exact ha (hsub S (mem_filter.mp hS).1 (mem_filter.mp hS).2.1)
      rw [hempty,card_empty]; exact ⟨0,rfl⟩
  · intro S hS
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hS
    change InducedDegreeTwo K (R \ (R \ T))
    rw [Finset.sdiff_sdiff_eq_self (f.subsets T hT)]
    exact f.cycles T hT

theorem residual_not_small {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (k : Nat)
    (f : ResidualPentagons K k) (hk : 0 < k) (heven : Even k) (hle : k ≤ 8) : False := by
  classical
  have hnonempty : f.family.Nonempty := card_pos.mp (by rw [f.card_family]; exact hk)
  obtain ⟨S,hS⟩ := hnonempty
  have h5 : 5 ≤ k := by
    have := card_le_card (f.subsets S hS)
    rw [f.sizes S hS,f.card_rows] at this
    exact this
  have hkcases : k = 6 ∨ k = 8 := by
    rw [Nat.even_iff] at heven
    omega
  rcases hkcases with rfl|rfl
  · exact no_six_pentagon_family K f.rows f.card_rows f.family f.card_family f.subsets f.sizes f.cycles
  · exact residual_not_eight K f

#print axioms residual_not_small
end PricingC.GParity
