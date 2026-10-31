import UniformK60.ABDEOwners

/-! Physical entry to the common support-word cover for all four strict
profiles. The selected mark keeps its actual critical-cell type. -/
set_option autoImplicit false
namespace UniformK60.ABDEEntrance
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationAdapter UniformK60.ClassificationGeometry
open UniformK60.PhysicalHelpers UniformK60.ABDERootPalette UniformK60.ABDEOwners
open PricingABD.ABLayout PricingABD.ABGeometry UniformK60.CommonBlocks
open UniformK60.CommonEntrance

def layoutProfile (profile : Fin 4) : Profile :=
  if profile=0 then .A else if profile=1 then .B else .D

def nativeTypes (t : Fin 3 → Bool) : Types := ⟨t 0,t 1,t 2⟩

theorem left_large (profile : Fin 4) (five : Bool) :
    leftLarge ⟨layoutProfile profile,five⟩=large profile 0 := by
  fin_cases profile <;> rfl

theorem right_large (profile : Fin 4) (five : Bool) :
    rightLarge ⟨layoutProfile profile,five⟩=large profile 1 := by
  fin_cases profile <;> rfl

noncomputable def from_cells {c : Host} {r : Vertex} {profile : Fin 4}
    (a : Cells c r profile) (five : Bool) (mark : Vertex)
    (hm : mark ∈ colorNeighborhood c (palette 3) r)
    (high : 15≤colorDegree c (palette 3) mark)
    (hs : (attachingSupport c r (palette 3) mark (palette 0)).card=
      freeSize ⟨layoutProfile profile,five⟩) :
    Blocks c ⟨layoutProfile profile,five⟩ (nativeTypes a.types) := by
  let m : PhysicalNeighborhoodMap c r (palette 1)
      (model (leftLarge ⟨layoutProfile profile,five⟩) (nativeTypes a.types).left) := by
    rw [left_large]
    exact a.cell 0
  let x : PhysicalNeighborhoodMap c r (palette 2)
      (model (rightLarge ⟨layoutProfile profile,five⟩) (nativeTypes a.types).right) := by
    rw [right_large]
    exact a.cell 1
  have hmp : m.colors=foreignEquiv 1 := by
    fin_cases profile <;> change (a.cell 0).colors=foreignEquiv 1 <;> exact a.palettes 0
  have hxp : x.colors=foreignEquiv 2 := by
    fin_cases profile <;> change (a.cell 1).colors=foreignEquiv 2 <;> exact a.palettes 1
  exact of_cells _ _ r mark m x hmp hxp hm high hs

/-- Complete supplied-root extraction, including equal-size template order,
a genuine mark and enumeration of its full free attaching support. -/
theorem actual_blocks (profile : Fin 4) (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hw : W c r=mass profile) (hh : mass profile≤H c r) :
    ∃ σ : FourColor ≃ FourColor,let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧
      (∀ q : Color,colorDegree d (palette q) r=shape profile q) ∧
      ∃ a : Cells d r profile,Ordered profile a.types ∧
      ∃ five : Bool,∃ b : Blocks d ⟨layoutProfile profile,five⟩ (nativeTypes a.types),
        b.root=r := by
  obtain ⟨σ,good,hd,hH⟩ := actual_root_ordered profile c hc r hw
  obtain ⟨τ,good',hH',hd',a,ho,mark,hm,high⟩ :=
    ordered_owner_with_mark _ good r profile hd (by rw [hH];exact hh)
  let d := relabel c (Equiv.refl _) (τ.trans σ)
  have hs := low_support_four_or_five d good' r mark hm high
  refine ⟨τ.trans σ,good',hH'.trans hH,hd',a,ho,?_⟩
  rcases hs with hs|hs
  · exact ⟨false,from_cells a false mark hm high hs,rfl⟩
  · exact ⟨true,from_cells a true mark hm high hs,rfl⟩

#print axioms actual_blocks
end UniformK60.ABDEEntrance
