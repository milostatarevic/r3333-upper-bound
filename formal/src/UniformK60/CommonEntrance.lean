import UniformK60.CommonSupportNormalization

set_option autoImplicit false
namespace UniformK60.CommonEntrance
open Ramsey61 Finset UniformK60.Physical UniformK60.ClassificationAdapter
open UniformK60.ClassificationGeometry UniformK60.PhysicalHelpers
open PricingABD.ABLayout PricingABD.ABGeometry UniformK60.CommonBlocks

/-- Enumerate the entire physical free support. Nothing is added to the
host and no attaching-support vertex is discarded. -/
noncomputable def of_cells {c : Host} (l : Layout) (types : Types) (r mark : Vertex)
    (left : PhysicalNeighborhoodMap c r (palette 1) (model (leftLarge l) types.left))
    (right : PhysicalNeighborhoodMap c r (palette 2) (model (rightLarge l) types.right))
    (hl : left.colors=foreignEquiv 1) (hr : right.colors=foreignEquiv 2)
    (hm : mark ∈ colorNeighborhood c (palette 3) r)
    (high : 15≤colorDegree c (palette 3) mark)
    (hs : (attachingSupport c r (palette 3) mark (palette 0)).card=freeSize l) :
    Blocks c l types := by
  classical
  let S := attachingSupport c r (palette 3) mark (palette 0)
  let e : S ≃ Fin (freeSize l) := Fintype.equivFinOfCardEq (by simpa [S] using hs)
  let f : Fin (freeSize l) ↪ Vertex :=
    ⟨fun i => (e.symm i).val,fun i j h => e.symm.injective (Subtype.ext h)⟩
  refine ⟨r,mark,f,left,right,hm,?_,hl,hr,high,?_,?_⟩
  · intro i; exact (mem_inter.mp (e.symm i).property).2
  · intro i
    exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp (e.symm i).property).1).2
  · intro v
    constructor
    · intro hv
      refine ⟨e ⟨v,hv⟩,?_⟩
      change (e.symm (e ⟨v,hv⟩)).val=v
      simp
    · rintro ⟨i,rfl⟩;exact (e.symm i).property

/-- The complete free support has size four or five for every high mark,
independently of the size or classification of the mark's root cell. -/
theorem low_support_four_or_five (c : Host) (hc : NoMonochromaticTriangle c)
    (r mark : Vertex) (hm : mark ∈ colorNeighborhood c (palette 3) r)
    (hh : 15≤colorDegree c (palette 3) mark) :
    (attachingSupport c r (palette 3) mark (palette 0)).card=4 ∨
      (attachingSupport c r (palette 3) mark (palette 0)).card=5 := by
  obtain ⟨p0,p1,p2,_,_,_,heq,hpat⟩ :=
    genuine_high_attaching_support_geometry c hc r (palette 3) mark hm hh
  have hmem : palette 0 ∈ ({p0,p1,p2} : Finset FourColor) := by rw [←heq];decide
  simp only [mem_insert,mem_singleton] at hmem
  unfold UniformK60.ClassificationGeometry.FourFivePattern at hpat
  rcases hmem with he|he|he <;> subst_vars <;> rcases hpat with h|h|h|h <;> omega

#print axioms of_cells
#print axioms low_support_four_or_five
end UniformK60.CommonEntrance
