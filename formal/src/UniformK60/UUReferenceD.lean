import UniformK60.UUCoordinates
import UniformK60.CommonSoundness
import UniformK60.UUSourceFacts

/-! For D/U/U, the sole missing reference position is an unused low vertex.
Assigning its incident edges color0 supplies reference facts, while the
sixty surviving vertices retain the actual host coloring exactly. -/
set_option autoImplicit false
namespace UniformK60.UUReferenceD
open Ramsey61 Finset UniformK60.Physical
open PricingABD.ABLayout
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonReference
open UniformK60.UnitRestriction UniformK60.ReferenceExtension
open UniformK61.UUSupportData UniformK61.UUPureCoordinates

variable {c : Host} {q : Bool} {p : Pair}

noncomputable def completed (b : Blocks c (layout p) ⟨false,false,q⟩)
    (h : Completion b none) : ReferenceColoring :=
  extend (coloring b h) 14 (fun _ => palette 0)

theorem agrees (b : Blocks c (layout p) ⟨false,false,q⟩) (h : Completion b none)
    (a d : Fin 61) (ha : a≠14) (hd : d≠14) :
    completed b h a d=referenceColoring b h a d := by
  rw [completed,extend_survivors _ _ _ _ _ ha hd]
  rfl

theorem restriction_good (b : Blocks c (layout p) ⟨false,false,q⟩) (h : Completion b none)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (restrictColoring (completed b h) 14) :=
  restrict_extend_good _ (coloring_good b h hc) _ _

theorem spokes (b : Blocks c (layout p) ⟨false,false,q⟩) (h : Completion b none)
    (v : Fin 61) (hv : v≠0) :
    completed b h 0 v=palette (UniformK61.UUSourceDefs.rootColor v) := by
  by_cases h14 : v=14
  · subst v
    simp [completed,extend,UniformK61.UUSourceDefs.rootColor]
  · obtain ⟨u,hu,hpos,hur,huv,huq⟩ := matching_spoke (UniformK61.UUSupportData.five p) v hv
    have hs : CommonSoundness.Retained (layout p) none u := by
      constructor
      · change u.u ≠ (14:Fin 61);rw [hur];decide
      · change u.v ≠ (14:Fin 61);rw [huv];exact h14
    have hm := matched_iff (referenceColoring b h) u (CommonSoundness.spokes_match b h u hu hs)
    have hedge := hm.mpr hpos
    rw [agrees b h 0 v (by decide) h14]
    simpa only [hur,huv,huq,CEncodingCore.palette,Physical.palette] using hedge

private theorem left_ne (a : Fin 15) : UniformK61.UUBridgeData.lVertex a≠14 := by
  intro he
  have hh:=congrArg Fin.val he
  dsimp [UniformK61.UUBridgeData.lVertex] at hh
  omega

private theorem right_ne (a : Fin 15) : UniformK61.UUBridgeData.rVertex a≠14 := by
  intro he
  have hh:=congrArg Fin.val he
  dsimp [UniformK61.UUBridgeData.rVertex] at hh
  omega

private theorem marked_ne (a : Fin 16) : UniformK61.UUBridgeData.qVertex a≠14 := by
  intro he
  have hh:=congrArg Fin.val he
  dsimp [UniformK61.UUBridgeData.qVertex] at hh
  omega

theorem static (b : Blocks c (layout p) ⟨false,false,q⟩) (h : Completion b none) :
    UniformK61.UUTemplateTransport.StaticHost q (completed b h) := by
  refine ⟨spokes b h,?_,?_,?_⟩
  · intro a d had
    rw [agrees b h _ _ (left_ne a) (left_ne d)]
    change c (referenceMap b h (CommonCoordinates.Reference.left (layout p) a))
      (referenceMap b h (CommonCoordinates.Reference.left (layout p) d))=_
    rw [referenceMap_left,referenceMap_left]
    have he := CommonBlocks.left_edges b a d had
    have hm : PricingABD.ABGeometry.model (leftLarge (layout p)) false a d =
        R4333.k15Template false a d := by rfl
    simpa only [frame,physical_left,hm,UniformK61.Core.palette,CEncodingCore.palette,Physical.palette] using he
  · intro a d had
    rw [agrees b h _ _ (right_ne a) (right_ne d)]
    change c (referenceMap b h (CommonCoordinates.Reference.right (layout p) a))
      (referenceMap b h (CommonCoordinates.Reference.right (layout p) d))=_
    rw [referenceMap_right,referenceMap_right]
    have he := CommonBlocks.right_edges b a d had
    have hm : PricingABD.ABGeometry.model (rightLarge (layout p)) false a d =
        R4333.k15Template false a d := by rfl
    simpa only [frame,physical_right,hm,UniformK61.Core.palette,CEncodingCore.palette,Physical.palette] using he
  · intro a d had
    rw [agrees b h _ _ (marked_ne a) (marked_ne d)]
    change c (referenceMap b h (CommonCoordinates.Reference.marked (layout p) (markedPosition none a)))
      (referenceMap b h (CommonCoordinates.Reference.marked (layout p) (markedPosition none d)))=_
    rw [referenceMap_marked,referenceMap_marked,h.marked.map_color a d had]
    have hf (k : Fin 3) : UniformK60.PhysicalHelpers.foreign 3 k=
        PricingABD.ABGeometry.foreign 3 k := by fin_cases k <;> rfl
    rw [hf]
    rfl

#print axioms static
#print axioms restriction_good
end UniformK60.UUReferenceD
