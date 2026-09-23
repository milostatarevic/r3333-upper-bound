import PricingC.SelectedTriple

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase Ramsey61.CAnchorGeometry
open PricingIntegration.SeedCensus

/-- All actual555/554/545 configurations enter one of the456 exact retained
state/map records. The chosen X,S,Y scopes use one host and palette throughout.
This supplies physical matrices and overlap identities; global gluing follows
in the final consumer. -/
theorem actual_C_supplies_aligned_triple (c : Host) (hc : NoMonochromaticTriangle c)
    (hroot : RootConditions c) (hmarked : 15 ≤ colorDegree c (palette 2) 33)
    (hshape : ThreeAnchorShapes c) :
    ∃ b : Boundary, Nonempty (AlignedTriple c b) := by
  classical
  obtain ⟨p⟩ := actual_C_supplies_XS_pair c hc hroot hmarked hshape
  rcases pair_three_domains c p hmarked with hall | ⟨o,ho,hdomain⟩ | ⟨o,ho,hdomain⟩
  · let b : Boundary := .inl (p.pair,0)
    let ap : AlignedPair c b := {
      physical := p
      pair_match := rfl
      present_match := by intro a; rw [hall]; simp [b,omitted] }
    obtain ⟨i,ht⟩ := complete_five_aligned c hc hroot b ap rfl
      (fun i => .inl (p.pair,i))
      (fun i => sameAnchor_eraseY (.inl (p.pair,i)))
      (fun _ => rfl) (fun _ => rfl)
    exact ⟨.inl (p.pair,i),ht⟩
  · have hcol := (mem_filter.mp ho).2
    obtain ⟨d,hd⟩ := (d_roles_exact p.pair o).mpr hcol
    let b : Boundary := .inr (.inl (p.pair,d,0))
    let ap : AlignedPair c b := {
      physical := p
      pair_match := rfl
      present_match := by intro a; rw [hdomain]; simp [b,omitted,hd,ne_comm] }
    obtain ⟨i,ht⟩ := complete_five_aligned c hc hroot b ap rfl
      (fun i => .inr (.inl (p.pair,d,i)))
      (fun i => sameAnchor_eraseY (.inr (.inl (p.pair,d,i))))
      (fun _ => rfl) (fun _ => rfl)
    exact ⟨.inr (.inl (p.pair,d,i)),ht⟩
  · have hcol := (mem_filter.mp ho).2
    obtain ⟨d,hd⟩ := (b_roles_exact p.pair o).mpr hcol
    let b : Boundary := .inr (.inr (.inl (p.pair,d,0)))
    let ap : AlignedPair c b := {
      physical := p
      pair_match := rfl
      present_match := by intro a; rw [hdomain]; simp [b,omitted,hd,ne_comm] }
    have hpsame : ∀ i : Fin 2, SameAnchor b (.inr (.inr (.inr (p.pair,d,i)))) := by
      intro i
      refine ⟨rfl,rfl,rfl,?_⟩
      intro j hj
      let k : Fin 4 := ⟨j.val,hj⟩
      have hk : k.castSucc = j := Fin.ext rfl
      have hh := star_plane_same_anchor p.pair d 0 i k
      have hk' : Fin.castLE (by decide : 4 ≤ 5) k = j := Fin.ext rfl
      rw [hk'] at hh
      exact hh.symm
    rcases complete_four_aligned c hc hroot b ap rfl
      (fun i => .inr (.inr (.inl (p.pair,d,i))))
      (fun i => .inr (.inr (.inr (p.pair,d,i))))
      (fun i => sameAnchor_eraseY (.inr (.inr (.inl (p.pair,d,i))))) hpsame
      (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (by intro i j; fin_cases j <;> rfl) with ⟨i,ht⟩ | ⟨i,ht⟩
    · exact ⟨.inr (.inr (.inl (p.pair,d,i))),ht⟩
    · exact ⟨.inr (.inr (.inr (p.pair,d,i))),ht⟩

#print axioms actual_C_supplies_aligned_triple
end PricingC
