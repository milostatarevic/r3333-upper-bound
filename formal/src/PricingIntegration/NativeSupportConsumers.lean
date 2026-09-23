import PricingIntegration.PhysicalForeignSupport
import PricingC.U15SupportCover
import PricingC.U16SupportCover
import PricingABD.T16SupportCover
set_option autoImplicit false
namespace PricingIntegration.NativeSupportConsumers
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingIntegration.BActualFrame PricingIntegration.PhysicalForeignSupport
open PricingIntegration.FixedPhysicalNeighborhood

/-- The finite support orbit action changes coordinates of the entire
physical critical cell, with all its original incident edges retained. -/
theorem realize_support_rep {n : Nat} {c : Host} {r mark : Vertex} {side : Bool}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) t)
    (e : Fin n ≃ Fin n) (hp : ∀a b,a≠b → t (e a) (e b)=t a b)
    (rep : Finset (Fin n)) (hs : (support m mark).image e=rep) :
    ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) t,
      z.colors=m.colors ∧ support z mark=rep := by
  have he : ∀a b,a≠b → modelInPalette m m.colors (e.symm a) (e.symm b)=t a b := by
    intro a b hab
    change m.colors.symm (m.colors (t (e.symm a) (e.symm b)))=_
    rw [Equiv.symm_apply_apply]
    have h := hp (e.symm a) (e.symm b) (e.symm.injective.ne hab)
    simpa only [Equiv.apply_symm_apply] using h.symm
  let z := mapOfNormalization m m.colors e.symm he
  refine ⟨z,rfl,?_⟩
  rw [←hs]
  ext i
  simp only [support,mem_filter,mem_univ,true_and,mem_image]
  change c mark (m.vertex (e.symm i))=palette 3 ↔ ∃a,c mark (m.vertex a)=palette 3 ∧ e a=i
  constructor
  · intro hi;exact ⟨e.symm i,hi,e.apply_symm_apply i⟩
  · rintro ⟨a,ha,he⟩;subst i;simpa only [Equiv.symm_apply_apply] using ha

theorem actual_u15_support_admitted {c : Host} {r mark : Vertex} {side : Bool}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k15Template false))
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hp : m.colors=foreignEquiv (owner side)) (hh : 15≤colorDegree c (palette 3) mark) :
    ((support m mark).card=4 ∧ ∃rep∈PricingC.U15SupportCover.representatives4,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k15Template false),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) ∨
    ((support m mark).card=5 ∧ ∃rep∈PricingC.U15SupportCover.representatives5,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k15Template false),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) := by
  rcases support_four_or_five m hc hm hh with h4|h5
  · have hproper : PricingC.U15SupportCover.ProperFour (support m mark) := actual_four_is_proper m hc hm hp hh h4
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingC.U15SupportCover.four_support_cover (support m mark) h4 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inl ⟨h4,rep,hrep,z,hz.trans hp,hzs⟩
  · have hproper : PricingC.U15SupportCover.ProperFive (support m mark) := support_independent m hc hm hp
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingC.U15SupportCover.five_support_cover (support m mark) h5 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inr ⟨h5,rep,hrep,z,hz.trans hp,hzs⟩
#print axioms actual_u15_support_admitted

theorem actual_t15_support_admitted {c : Host} {r mark : Vertex} {side : Bool}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k15Template true))
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hp : m.colors=foreignEquiv (owner side)) (hh : 15≤colorDegree c (palette 3) mark) :
    ((support m mark).card=4 ∧ ∃rep∈PricingABD.FiniteSupportsFast.representatives4,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k15Template true),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) ∨
    ((support m mark).card=5 ∧ ∃rep∈PricingABD.FiniteSupportsFast.representatives5,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k15Template true),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) := by
  rcases support_four_or_five m hc hm hh with h4|h5
  · have hproper : PricingABD.FiniteSupportsFast.ProperFour (support m mark) := actual_four_is_proper m hc hm hp hh h4
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingABD.FiniteSupportsFast.four_support_cover (support m mark) h4 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inl ⟨h4,rep,hrep,z,hz.trans hp,hzs⟩
  · have hproper : PricingABD.FiniteSupportsFast.ProperFive (support m mark) := support_independent m hc hm hp
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingABD.FiniteSupportsFast.five_support_cover (support m mark) h5 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inr ⟨h5,rep,hrep,z,hz.trans hp,hzs⟩
#print axioms actual_t15_support_admitted

theorem actual_u16_support_admitted {c : Host} {r mark : Vertex} {side : Bool}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k16Template false))
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hp : m.colors=foreignEquiv (owner side)) (hh : 15≤colorDegree c (palette 3) mark) :
    ((support m mark).card=4 ∧ ∃rep∈PricingC.U16SupportCover.representatives4,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k16Template false),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) ∨
    ((support m mark).card=5 ∧ ∃rep∈PricingC.U16SupportCover.representatives5,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k16Template false),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) := by
  rcases support_four_or_five m hc hm hh with h4|h5
  · have hproper : PricingC.U16SupportCover.ProperFour (support m mark) := actual_four_is_proper m hc hm hp hh h4
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingC.U16SupportCover.four_support_cover (support m mark) h4 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inl ⟨h4,rep,hrep,z,hz.trans hp,hzs⟩
  · have hproper : PricingC.U16SupportCover.ProperFive (support m mark) := support_independent m hc hm hp
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingC.U16SupportCover.five_support_cover (support m mark) h5 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inr ⟨h5,rep,hrep,z,hz.trans hp,hzs⟩
#print axioms actual_u16_support_admitted

theorem actual_t16_support_admitted {c : Host} {r mark : Vertex} {side : Bool}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k16Template true))
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hp : m.colors=foreignEquiv (owner side)) (hh : 15≤colorDegree c (palette 3) mark) :
    ((support m mark).card=4 ∧ ∃rep∈PricingABD.T16SupportCover.representatives4,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k16Template true),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) ∨
    ((support m mark).card=5 ∧ ∃rep∈PricingABD.T16SupportCover.representatives5,
      ∃z : PhysicalNeighborhoodMap c r (palette (owner side)) (R4333.k16Template true),
        z.colors=foreignEquiv (owner side) ∧ support z mark=rep) := by
  rcases support_four_or_five m hc hm hh with h4|h5
  · have hproper : PricingABD.T16SupportCover.ProperFour (support m mark) := actual_four_is_proper m hc hm hp hh h4
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingABD.T16SupportCover.four_support_cover (support m mark) h4 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inl ⟨h4,rep,hrep,z,hz.trans hp,hzs⟩
  · have hproper : PricingABD.T16SupportCover.ProperFive (support m mark) := support_independent m hc hm hp
    obtain ⟨rep,hrep,e,he,hs⟩ := PricingABD.T16SupportCover.five_support_cover (support m mark) h5 hproper
    obtain ⟨z,hz,hzs⟩ := realize_support_rep m e he rep hs
    exact Or.inr ⟨h5,rep,hrep,z,hz.trans hp,hzs⟩
#print axioms actual_t16_support_admitted

end PricingIntegration.NativeSupportConsumers
