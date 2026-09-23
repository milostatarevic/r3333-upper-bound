import PricingG.SupportSaturation

namespace PricingG
open Finset

private theorem triple_of_pair {V : Type*} [DecidableEq V]
    (S : Finset V) (hS : S.card = 3) (a b : V) (hab : a ≠ b)
    (ha : a ∈ S) (hb : b ∈ S) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ S = {a, b, c} := by
  have hb' : b ∈ S.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  have he : ((S.erase a).erase b).card = 1 := by
    rw [card_erase_of_mem hb', card_erase_of_mem ha, hS]
  obtain ⟨c, hc⟩ := card_eq_one.mp he
  have hcm : c ∈ (S.erase a).erase b := by rw [hc]; simp
  have hca : c ≠ a := (mem_erase.mp (mem_erase.mp hcm).2).1
  have hcb : c ≠ b := (mem_erase.mp hcm).1
  refine ⟨c, hca, hcb, ?_⟩
  calc
    S = insert a (S.erase a) := (insert_erase ha).symm
    _ = insert a (insert b ((S.erase a).erase b)) := by rw [insert_erase hb']
    _ = {a, b, c} := by rw [hc]

private theorem another_triple_through_pair {V : Type*} [DecidableEq V]
    (F : Finset (Finset V))
    (hrows : ∀ a b, a ≠ b → Even (F.filter fun S => a ∈ S ∧ b ∈ S).card)
    (S : Finset V) (hS : S ∈ F) (a b : V) (hab : a ≠ b)
    (ha : a ∈ S) (hb : b ∈ S) :
    ∃ T ∈ F, T ≠ S ∧ a ∈ T ∧ b ∈ T := by
  let P := F.filter fun T => a ∈ T ∧ b ∈ T
  have hSP : S ∈ P := mem_filter.mpr ⟨hS, ha, hb⟩
  have hp : 0 < P.card := card_pos.mpr ⟨S, hSP⟩
  obtain ⟨k, hk⟩ := hrows a b hab
  have htwo : 1 < P.card := by change P.card = k + k at hk; omega
  obtain ⟨T, hT, hne⟩ := exists_mem_ne htwo S
  exact ⟨T, (mem_filter.mp hT).1, hne, (mem_filter.mp hT).2⟩

/-- Orthogonal weight-three columns necessarily generate every triple of a
four-point block. Both row and column parity are explicit mathematical premises. -/
theorem orthogonal_triples_contains_four_block {V : Type*} [DecidableEq V]
    (F : Finset (Finset V))
    (hsize : ∀ S ∈ F, S.card = 3)
    (hcols : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Even (S ∩ T).card)
    (hrows : ∀ a b, a ≠ b → Even (F.filter fun S => a ∈ S ∧ b ∈ S).card)
    (S : Finset V) (hS : S ∈ F) :
    ∃ a b c d : V,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      S = {a,b,c} ∧ {a,b,d} ∈ F ∧ {a,c,d} ∈ F ∧ {b,c,d} ∈ F := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp (hsize S hS)
  obtain ⟨T,hT,hTS,haT,hbT⟩ := another_triple_through_pair F hrows {a,b,c} hS a b hab (by simp) (by simp)
  obtain ⟨d,hda,hdb,rfl⟩ := triple_of_pair T (hsize T hT) a b hab haT hbT
  have hdc : d ≠ c := by intro h; subst d; exact hTS rfl
  obtain ⟨U,hU,hUS,haU,hcU⟩ := another_triple_through_pair F hrows {a,b,c} hS a c hac (by simp) (by simp)
  obtain ⟨e,hea,hec,rfl⟩ := triple_of_pair U (hsize U hU) a c hac haU hcU
  have heb : e ≠ b := by
    intro h; subst e
    exact hUS (by ext z; simp [or_left_comm, or_assoc, or_comm])
  have hed : e = d := by
    by_contra hed
    have hUT : ({a,c,e} : Finset V) ≠ {a,b,d} := by
      intro h
      have : c ∈ ({a,b,d} : Finset V) := by rw [← h]; simp
      simp [hac.symm, hbc.symm, hdc.symm] at this
    have hp := hcols {a,c,e} hU {a,b,d} hT hUT
    have hi : ({a,c,e} : Finset V) ∩ {a,b,d} = {a} := by
      ext z
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h1,h2⟩
        rcases h1 with rfl | rfl | rfl <;> rcases h2 with h | h | h <;> simp_all [eq_comm]
      · intro h; subst z; simp
    rw [hi] at hp
    norm_num at hp
  subst e
  obtain ⟨U,hU2,hUS,hbU,hcU⟩ := another_triple_through_pair F hrows {a,b,c} hS b c hbc (by simp) (by simp)
  obtain ⟨e,heb,hec,rfl⟩ := triple_of_pair U (hsize U hU2) b c hbc hbU hcU
  have hea : e ≠ a := by
    intro h; subst e
    exact hUS (by ext z; simp [or_left_comm, or_assoc, or_comm])
  have hed : e = d := by
    by_contra hed
    have hUT : ({b,c,e} : Finset V) ≠ {a,b,d} := by
      intro h
      have : c ∈ ({a,b,d} : Finset V) := by rw [← h]; simp
      simp [hac.symm, hbc.symm, hdc.symm] at this
    have hp := hcols {b,c,e} hU2 {a,b,d} hT hUT
    have hi : ({b,c,e} : Finset V) ∩ {a,b,d} = {b} := by
      ext z
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h1,h2⟩
        rcases h1 with rfl | rfl | rfl <;> rcases h2 with h | h | h <;> simp_all [eq_comm]
      · intro h; subst z; simp
    rw [hi] at hp
    norm_num at hp
  subst e
  exact ⟨a,b,c,d,hab,hac,hda.symm,hbc,hdb.symm,hdc.symm,rfl,hT,hU,hU2⟩

#print axioms orthogonal_triples_contains_four_block
end PricingG
