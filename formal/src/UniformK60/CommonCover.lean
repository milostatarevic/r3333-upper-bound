import UniformK60.CommonSoundness
import UniformK60.CommonCompletion
import UniformK60.CommonWordCover
import UniformK60.EFormula

/-! Compose actual root extraction, the closed finite support/word cover,
marked-cell placement and fresh K60 formulas. The separate U/U679 branch
is kept explicit and is not assumed to belong to the common737 tables. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.CommonCover
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationMarks UniformK60.ABDERootPalette
open UniformK60.ABDEOwners UniformK60.ABDEEntrance
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonCompletion
open UniformK60.CommonWordCover UniformK60.CommonSoundness
open PricingABD.ABLayout

private theorem omission_positions_cover : ∀ (t : Bool) (k : Fin 15),
    k∈markRepresentatives t → ∃ i : Fin (EFormula.omissionCount t),
      EFormula.omissionPosition t i=k := by decide

/-- Any actual common-owner configuration reaches one exact A/B/D or E
formula. Every finite normalization and physical placement is a conclusion. -/
theorem physical_common_formula {c : Host} {r : Vertex} {profile : Fin 4} {five : Bool}
    (hc : NoMonochromaticTriangle c) (a : Cells c r profile)
    (horder : Ordered profile a.types)
    (hd : colorDegree c (palette 0) r=shape profile 0)
    (b : Blocks c ⟨layoutProfile profile,five⟩ (nativeTypes a.types)) (hr : b.root=r)
    (ho : CompletionC.CommonCases.NativeOwner ⟨layoutProfile profile,five⟩ (nativeTypes a.types)) :
    if profile=3 then
      ∃ k : EFormula.Case,∃ w : DenseCounter.Valuation,DenseCounter.FormulaSat w (EFormula.formula k)
    else
      ∃ k : ABDFormula.Case,∃ w : DenseCounter.Valuation,DenseCounter.FormulaSat w (ABDFormula.formula k) := by
  obtain ⟨σ,good,hσ,w,hwroot,_,p,hp,hf,hpair,j,z,hzroot,_,hg,hmat,hl,hrr⟩ :=
    physical_word_cover b hc ho
  have h0 : σ (palette 0)=palette 0 := by rcases hσ with rfl|rfl <;> rfl
  have h3 : σ (palette 3)=palette 3 := by rcases hσ with rfl|rfl <;> rfl
  obtain ⟨missing,⟨completion⟩,hE,hABD⟩ :=
    after_word a hd σ h0 h3 z (hzroot.trans hr)
  obtain ⟨valuation,hsat⟩ := common_restriction_satisfiable w z completion good p hf hpair j hg hmat hl hrr
  let key : ABDFormula.CommonCase := ⟨⟨layoutProfile profile,five⟩,nativeTypes a.types,⟨p,hp⟩,j⟩
  by_cases hprofile : profile=3
  · simp only [hprofile,if_pos]
    obtain ⟨k,hk,hm⟩ := hE hprofile
    subst missing
    have hright : a.types 1=true := by
      simpa [CompletionC.CommonCases.NativeOwner,layoutProfile,hprofile,nativeTypes] using ho
    have hmarked : a.types 2=true := by
      have hs : (a.types 0=false ∨ a.types 1=true) ∧
          (a.types 1=false ∨ a.types 2=true) := by
        simpa [Ordered,hprofile] using horder
      rcases hs.2 with hh|hh
      · simp [hright] at hh
      · exact hh
    rw [hmarked] at hk
    obtain ⟨i,hi⟩ := omission_positions_cover true k hk
    let source : EFormula.MixedSource := ⟨key,by
      constructor
      · change layoutProfile profile=.D
        rw [hprofile]
        rfl
      · exact hmarked⟩
    refine ⟨Sum.inr (source,i),valuation,?_⟩
    have hdelete : EFormula.omission true i=omission ⟨layoutProfile profile,five⟩ (some k) := by
      apply Fin.ext
      change 45+(EFormula.omissionPosition true i).val=45+k.val
      rw [hi]
    change DenseCounter.FormulaSat valuation
      (Core.formula (UnitRestriction.sortedRestriction (EFormula.omission true i)
        (ABDFormula.commonReferenceUnits key)))
    rw [hdelete]
    exact hsat
  · simp only [hprofile]
    have hm := hABD hprofile
    subst missing
    exact ⟨Sum.inl key,valuation,hsat⟩

private theorem A_native_owner {t : Fin 3 → Bool} {five : Bool}
    (h : Ordered 0 t) : CompletionC.CommonCases.NativeOwner ⟨.A,five⟩ (nativeTypes t) := by
  simpa [Ordered,CompletionC.CommonCases.NativeOwner,nativeTypes] using h

private theorem B_native_owner {t : Fin 3 → Bool} {five : Bool}
    (h : Ordered 1 t) : CompletionC.CommonCases.NativeOwner ⟨.B,five⟩ (nativeTypes t) := by
  simpa [Ordered,CompletionC.CommonCases.NativeOwner,nativeTypes] using h

/-- A supplied A violation reaches the exact frozen A/B/D input boundary. -/
theorem actual_A_cover (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=48) (hh : 48≤H c r) :
    ∃ k : ABDFormula.Case,∃ w : DenseCounter.Valuation,DenseCounter.FormulaSat w (ABDFormula.formula k) := by
  obtain ⟨σ,good,_,hd,a,ho,five,b,hr⟩ := actual_blocks 0 c hc r hw hh
  exact physical_common_formula good a ho (hd 0) b hr (A_native_owner ho)

/-- A supplied B violation reaches the exact frozen A/B/D input boundary. -/
theorem actual_B_cover (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=47) (hh : 47≤H c r) :
    ∃ k : ABDFormula.Case,∃ w : DenseCounter.Valuation,DenseCounter.FormulaSat w (ABDFormula.formula k) := by
  obtain ⟨σ,good,_,hd,a,ho,five,b,hr⟩ := actual_blocks 1 c hc r hw hh
  exact physical_common_formula good a ho (hd 0) b hr (B_native_owner ho)

/-- The only D branch left to the679-leaf construction is foreign U/U.
All mixed foreign owners are closed by the actual common cover above. -/
theorem actual_D_cover_or_UU (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=46) (hh : 46≤H c r) :
    ∃ σ : FourColor ≃ FourColor,let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧
      (∀ q : Color,colorDegree d (palette q) r=shape 2 q) ∧
      ∃ a : Cells d r 2,Ordered 2 a.types ∧
      ∃ five : Bool,∃ b : Blocks d ⟨.D,five⟩ (nativeTypes a.types),b.root=r ∧
      ((a.types 0=false ∧ a.types 1=false) ∨
        ∃ k : ABDFormula.Case,∃ w : DenseCounter.Valuation,DenseCounter.FormulaSat w (ABDFormula.formula k)) := by
  obtain ⟨σ,good,hH,hd,a,ho,five,b,hr⟩ := actual_blocks 2 c hc r hw hh
  refine ⟨σ,good,hH,hd,a,ho,five,b,hr,?_⟩
  cases ht : a.types 1 with
  | false =>
    left
    have hh : a.types 0=false ∨ a.types 1=true := by simpa [Ordered] using ho
    exact ⟨hh.resolve_right (by simp [ht]),rfl⟩
  | true =>
    right
    have hnative : CompletionC.CommonCases.NativeOwner ⟨.D,five⟩ (nativeTypes a.types) := ht
    exact physical_common_formula good a ho (hd 0) b hr hnative

/-- E uses the same common support words for mixed foreign owners; its two
foreign-U/U owners retain the explicit679-leaf branch. -/
theorem actual_E_cover_or_UU (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=45) (hh : 45≤H c r) :
    ∃ σ : FourColor ≃ FourColor,let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧
      (∀ q : Color,colorDegree d (palette q) r=shape 3 q) ∧
      ∃ a : Cells d r 3,Ordered 3 a.types ∧
      ∃ five : Bool,∃ b : Blocks d ⟨.D,five⟩ (nativeTypes a.types),b.root=r ∧
      ((a.types 0=false ∧ a.types 1=false) ∨
        ∃ k : EFormula.Case,∃ w : DenseCounter.Valuation,DenseCounter.FormulaSat w (EFormula.formula k)) := by
  obtain ⟨σ,good,hH,hd,a,ho,five,b,hr⟩ := actual_blocks 3 c hc r hw hh
  refine ⟨σ,good,hH,hd,a,ho,five,b,hr,?_⟩
  cases ht : a.types 1 with
  | false =>
    left
    have hh : (a.types 0=false ∨ a.types 1=true) ∧
        (a.types 1=false ∨ a.types 2=true) := by simpa [Ordered] using ho
    exact ⟨hh.1.resolve_right (by simp [ht]),rfl⟩
  | true =>
    right
    have hnative : CompletionC.CommonCases.NativeOwner ⟨.D,five⟩ (nativeTypes a.types) := ht
    exact physical_common_formula good a ho (hd 0) b hr hnative

#print axioms physical_common_formula
#print axioms actual_A_cover
#print axioms actual_B_cover
end UniformK60.CommonCover
