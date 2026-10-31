import UniformK60.CEntranceRealization

set_option autoImplicit false
namespace UniformK60.CEntranceWordCover
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CommonBlocks UniformK60.CommonWordCover UniformK60.CommonExchange
open UniformK60.CEntranceSource UniformK60.CEntranceCanonical UniformK60.CEntranceRealization
open CompletionC.NativeMatrices

/-- Every actual A/B entrance configuration reaches an eligible canonical
source word. All finite support/word choices and the physical witness are
conclusions of the theorem. -/
theorem actual_source {c : Host} {mode : Mode} {five : Bool}
    {t : PricingABD.ABLayout.Types} (b : Blocks c (layout mode five) t)
    (hc : NoMonochromaticTriangle c)
    (hd : ∀ q : Color,colorDegree c (palette q) b.root=CEntranceLayout.shape mode q)
    (owner : CompletionC.CommonCases.NativeOwner (layout mode five) t) :
    ∃ p : Fin 737,∃ j : Fin (pairTable p).count,Eligible mode p ∧
      ∃ d : Host,SourceWitness mode p j d := by
  obtain ⟨σ,good,hσ,w,_,_,p,_,hf,hp,j,z,hzr,_,_,hmat,hl,hr⟩ :=
    physical_word_cover b hc owner
  have h0 : σ (palette 0)=palette 0 := by rcases hσ with rfl|rfl <;> rfl
  have h3 : σ (palette 3)=palette 3 := by rcases hσ with rfl|rfl <;> rfl
  have hleft : colorDegree (relabel c (Equiv.refl _) σ) (palette 1) z.root=
      PricingABD.ABLayout.leftSize (layout mode five) := by
    have h := Fintype.card_congr z.left.neighborhoodEquiv
    have hn : (if PricingABD.ABLayout.leftLarge (layout mode five) then 16 else 15)=PricingABD.ABLayout.leftSize (layout mode five) := by
      fin_cases mode <;> cases five <;> rfl
    simpa only [Fintype.card_fin,Fintype.card_coe,colorDegree,hn] using h.symm
  have hright : colorDegree (relabel c (Equiv.refl _) σ) (palette 2) z.root=16 := by
    have h := Fintype.card_congr z.right.neighborhoodEquiv
    have hn : (if PricingABD.ABLayout.rightLarge (layout mode five) then 16 else 15)=PricingABD.ABLayout.rightSize (layout mode five) := by
      fin_cases mode <;> cases five <;> rfl
    have h' : colorDegree (relabel c (Equiv.refl _) σ) (palette 2) z.root=
        PricingABD.ABLayout.rightSize (layout mode five) := by
      simpa only [Fintype.card_fin,Fintype.card_coe,colorDegree,hn] using h.symm
    exact h'.trans (right_size mode five)
  have hzdegree : ∀ q : Color,colorDegree (relabel c (Equiv.refl _) σ) (palette q) z.root=
      CEntranceLayout.shape mode q := by
    intro q
    fin_cases q
    · change colorDegree (relabel c (Equiv.refl _) σ) (palette 0) z.root=CEntranceLayout.shape mode 0
      rw [relabel_degree]
      change colorDegree c (σ (palette 0)) z.root=CEntranceLayout.shape mode 0
      rw [h0,hzr]
      exact hd 0
    · change colorDegree (relabel c (Equiv.refl _) σ) (palette 1) z.root=CEntranceLayout.shape mode 1
      rw [hleft,left_size]
      fin_cases mode <;> rfl
    · change colorDegree (relabel c (Equiv.refl _) σ) (palette 2) z.root=CEntranceLayout.shape mode 2
      rw [hright]
      fin_cases mode <;> rfl
    · change colorDegree (relabel c (Equiv.refl _) σ) (palette 3) z.root=CEntranceLayout.shape mode 3
      rw [relabel_degree]
      change colorDegree c (σ (palette 3)) z.root=CEntranceLayout.shape mode 3
      rw [h3,hzr]
      exact hd 3
  exact ⟨p,j,(source_types w p hp).2.2,realize w z good hzdegree p hf hp j hmat hl hr⟩

#print axioms actual_source
end UniformK60.CEntranceWordCover
