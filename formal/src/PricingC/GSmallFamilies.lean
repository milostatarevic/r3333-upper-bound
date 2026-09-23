import PricingG.EightPentagons

namespace PricingC.GParity
open Finset PricingG

 theorem no_six_delete_one_pentagons {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (R : Finset V) (hR : R.card = 6)
    (hcyc : ∀ v ∈ R, InducedDegreeTwo K (R.erase v)) : False := by
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < R.card by omega)
  obtain ⟨v,hv,hva⟩ := exists_mem_ne (show 1 < R.card by omega) a
  have hav : a ∈ R.erase v := mem_erase.mpr ⟨Ne.symm hva,ha⟩
  have htwo := hcyc v hv a hav
  obtain ⟨b,hb⟩ := card_pos.mp (show 0 < ((R.erase v).filter fun b => K.Adj a b).card by omega)
  have hbR := (mem_erase.mp (mem_filter.mp hb).1).2
  have hab := (mem_filter.mp hb).2
  have habne : a ≠ b := K.ne_of_adj hab
  let N := R.filter fun b => K.Adj a b
  have hbN : b ∈ N := mem_filter.mpr ⟨hbR,hab⟩
  have hthree : N.card = 3 := by
    have h := hcyc b hbR a (mem_erase.mpr ⟨habne,ha⟩)
    rw [filter_erase,card_erase_of_mem hbN] at h
    have hn := card_pos.mpr ⟨b,hbN⟩
    omega
  have hall : ∀ w ∈ R, w ≠ a → K.Adj a w := by
    intro w hw hwa
    by_contra hn
    have h := hcyc w hw a (mem_erase.mpr ⟨Ne.symm hwa,ha⟩)
    rw [filter_erase,erase_eq_of_notMem (by simp only [mem_filter,hn,and_false]; exact not_false)] at h
    change N.card = 2 at h
    omega
  have heq : N = R.erase a := by
    ext w
    constructor
    · intro hw
      have hh := mem_filter.mp hw
      exact mem_erase.mpr ⟨(K.ne_of_adj hh.2).symm,hh.1⟩
    · intro hw
      have hh := mem_erase.mp hw
      exact mem_filter.mpr ⟨hh.2,hall w hh.2 hh.1⟩
  have hc : N.card = 5 := by rw [heq,card_erase_of_mem ha,hR]
  omega

 theorem no_six_pentagon_family {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (R : Finset V) (hR : R.card = 6)
    (F : Finset (Finset V)) (hF : F.card = 6)
    (hsub : ∀ S ∈ F, S ⊆ R) (hsize : ∀ S ∈ F, S.card = 5)
    (hcyc : ∀ S ∈ F, InducedDegreeTwo K S) : False := by
  have heq : F = R.powersetCard 5 := by
    apply eq_of_subset_of_card_le
    · intro S hS; exact mem_powersetCard.mpr ⟨hsub S hS,hsize S hS⟩
    · rw [card_powersetCard,hR,hF]; decide
  apply no_six_delete_one_pentagons K R hR
  intro v hv
  apply hcyc
  rw [heq]
  exact mem_powersetCard.mpr ⟨erase_subset _ _,by rw [card_erase_of_mem hv,hR]⟩

/-- Relative-universe form of the eight-column contradiction. It retains
the actual K graph on the residual physical rows, without any relabeling. -/
 theorem no_eight_relative_pentagon_complements {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (R : Finset V) (hR : R.card = 8)
    (F : Finset (Finset V)) (hF : F.card = 8)
    (hsub : ∀ S ∈ F, S ⊆ R) (hsize : ∀ S ∈ F, S.card = 3)
    (hcols : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Even (S ∩ T).card)
    (hrows : ∀ a b, a ≠ b → Even (F.filter fun S => a ∈ S ∧ b ∈ S).card)
    (hcycles : ∀ S ∈ F, InducedDegreeTwo K (R \ S)) : False := by
  obtain ⟨A,hA,hblock,hpartition⟩ := orthogonal_triples_has_block F
    (card_pos.mp (by omega)) hsize hcols hrows
  have hAR : A ⊆ R := by
    intro a ha
    obtain ⟨b,hb,hba⟩ := exists_mem_ne (show 1 < A.card by omega) a
    exact hsub (A.erase b) (hblock b hb) (mem_erase.mpr ⟨Ne.symm hba,ha⟩)
  let B := R \ A
  have hB : B.card = 4 := by rw [card_sdiff_of_subset hAR,hR,hA]
  have hdis : Disjoint A B := disjoint_sdiff_self_right
  have hFs : F ⊆ A.powersetCard 3 ∪ B.powersetCard 3 := by
    intro T hT
    rcases hpartition T hT with h | h
    · exact mem_union_left _ (mem_powersetCard.mpr ⟨h,hsize T hT⟩)
    · apply mem_union_right
      apply mem_powersetCard.mpr
      refine ⟨?_,hsize T hT⟩
      intro x hx
      exact mem_sdiff.mpr ⟨hsub T hT hx,fun ha => disjoint_left.mp h hx ha⟩
  have hFd : Disjoint (A.powersetCard 3) (B.powersetCard 3) := by
    apply disjoint_left.mpr
    intro T ha hb
    obtain ⟨x,hx⟩ := card_pos.mp (show 0 < T.card by rw [(mem_powersetCard.mp ha).2]; decide)
    exact disjoint_left.mp hdis ((mem_powersetCard.mp ha).1 hx) ((mem_powersetCard.mp hb).1 hx)
  have hFeq : F = A.powersetCard 3 ∪ B.powersetCard 3 := by
    apply eq_of_subset_of_card_le hFs
    rw [card_union_of_disjoint hFd,card_powersetCard,card_powersetCard,hA,hB,hF]
    decide
  have hRsplit : R = A ∪ B := (union_sdiff_of_subset hAR).symm
  have hdelA : ∀ a ∈ A, R \ A.erase a = insert a B := by
    intro a ha
    ext x
    by_cases hx : x ∈ A
    · have hxR := hAR hx
      simp [mem_sdiff,mem_erase,hx,hxR,B,eq_comm]
    · have hxa : x ≠ a := by intro e; exact hx (e ▸ ha)
      simp [mem_sdiff,mem_erase,hx,hxa,B]
  have hdelB : ∀ b ∈ B, R \ B.erase b = insert b A := by
    intro b hb
    ext x
    by_cases hx : x ∈ B
    · have hxR := (mem_sdiff.mp hx).1
      have hxA := (mem_sdiff.mp hx).2
      simp [mem_sdiff,mem_erase,hx,hxR,hxA,eq_comm]
    · have hxb : x ≠ b := by intro e; exact hx (e ▸ hb)
      have hxiff : x ∈ R ↔ x ∈ A := by rw [hRsplit]; simp [hx]
      simp [mem_sdiff,mem_erase,hx,hxb,hxiff]
  apply no_two_four_blocks_of_degree_two K A B hA hB hdis
  · intro a ha
    rw [←hdelA a ha]
    exact hcycles (A.erase a) (hblock a ha)
  · intro b hb
    rw [←hdelB b hb]
    apply hcycles
    rw [hFeq]
    exact mem_union_right _ (mem_powersetCard.mpr ⟨erase_subset _ _,by rw [card_erase_of_mem hb,hB]⟩)

#print axioms no_six_pentagon_family
#print axioms no_eight_relative_pentagon_complements
end PricingC.GParity
