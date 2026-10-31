import UniformK60.UUReferenceD
import UniformK60.UUE

set_option autoImplicit false
namespace UniformK60.UUReferenceE
open Ramsey61 Finset UniformK60.Physical
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonReference
open UniformK60.UnitRestriction UniformK60.ReferenceExtension
open UniformK61.UUSupportData UniformK61.UUPureCoordinates UniformK61.UUBridgeData

variable {c : Host} {q : Bool} {p : Pair}

def incident (q : Bool) (r : Fin 15) (v : Fin 61) : FourColor :=
  if v=0 then palette 3
  else if h : 45≤v.val then
    palette (PricingABD.ABGeometry.foreign 3
      (R4333.k16Template q r.castSucc ⟨v.val-45,by have := v.isLt;omega⟩))
  else palette 0

noncomputable def completed (b : Blocks c (layout p) ⟨false,false,q⟩) (r : Fin 15)
    (h : Completion b (some r)) : ReferenceColoring :=
  extend (coloring b h) (UUE.omitted r) (fun v => incident q r ((UUE.omitted r).castSucc.succAbove v))

theorem agrees (b : Blocks c (layout p) ⟨false,false,q⟩) (r : Fin 15)
    (h : Completion b (some r)) (a d : Fin 61)
    (ha : a≠(UUE.omitted r).castSucc) (hd : d≠(UUE.omitted r).castSucc) :
    completed b r h a d=referenceColoring b h a d := by
  rw [completed,extend_survivors _ _ _ _ _ ha hd]
  rfl

theorem missing_edge (b : Blocks c (layout p) ⟨false,false,q⟩) (r : Fin 15)
    (h : Completion b (some r)) (v : Fin 61) (hv : v≠(UUE.omitted r).castSucc) :
    completed b r h (UUE.omitted r).castSucc v=incident q r v := by
  rw [completed,extend_omitted,Fin.succAbove_predAbove hv]

theorem small_ne (r : Fin 15) (v : Fin 61) (hv : v.val≤44) :
    v≠(UUE.omitted r).castSucc := by
  intro he
  have := congrArg Fin.val he
  change v.val=45+r.val at this
  omega

theorem marked_ne (r : Fin 15) (a : Fin 16) (ha : a≠r.castSucc) :
    qVertex a≠(UUE.omitted r).castSucc := by
  intro he
  apply ha
  apply Fin.ext
  change a.val=r.val
  have := congrArg Fin.val he
  dsimp [qVertex,UUE.omitted] at this
  omega

theorem restriction_good (b : Blocks c (layout p) ⟨false,false,q⟩) (r : Fin 15)
    (h : Completion b (some r)) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (restrictColoring (completed b r h) (UUE.omitted r)) :=
  restrict_extend_good _ (coloring_good b h hc) _ _

theorem spokes (b : Blocks c (layout p) ⟨false,false,q⟩) (r : Fin 15)
    (h : Completion b (some r)) (v : Fin 61) (hv : v≠0) :
    completed b r h 0 v=palette (UniformK61.UUSourceDefs.rootColor v) := by
  by_cases hd : v=(UUE.omitted r).castSucc
  · subst v
    rw [(completed b r h).color_symm,missing_edge b r h 0 (small_ne r 0 (by decide))]
    simp [incident,UniformK61.UUSourceDefs.rootColor,UUE.omitted]
    split_ifs <;> first | rfl | omega
  · obtain ⟨u,hu,hpos,hur,huv,huq⟩ := matching_spoke (UniformK61.UUSupportData.five p) v hv
    have hs : CommonSoundness.Retained (layout p) (some r) u := by
      constructor
      · change u.u≠(UUE.omitted r).castSucc
        rw [hur];exact small_ne r 0 (by decide)
      · change u.v≠(UUE.omitted r).castSucc
        rw [huv];exact hd
    have hedge := (matched_iff (referenceColoring b h) u
      (CommonSoundness.spokes_match b h u hu hs)).mpr hpos
    rw [agrees b r h 0 v (small_ne r 0 (by decide)) hd]
    simpa only [hur,huv,huq,CEncodingCore.palette,Physical.palette] using hedge

theorem static (b : Blocks c (layout p) ⟨false,false,q⟩) (r : Fin 15)
    (h : Completion b (some r)) :
    UniformK61.UUTemplateTransport.StaticHost q (completed b r h) := by
  refine ⟨spokes b r h,?_,?_,?_⟩
  · intro a d had
    rw [agrees b r h _ _ (small_ne r _ (by dsimp [lVertex];omega))
      (small_ne r _ (by dsimp [lVertex];omega))]
    change c (referenceMap b h (CommonCoordinates.Reference.left (layout p) a))
      (referenceMap b h (CommonCoordinates.Reference.left (layout p) d))=_
    rw [referenceMap_left,referenceMap_left]
    have he := CommonBlocks.left_edges b a d had
    have hm : PricingABD.ABGeometry.model (PricingABD.ABLayout.leftLarge (layout p)) false a d=
        R4333.k15Template false a d := by rfl
    simpa only [frame,physical_left,hm,UniformK61.Core.palette,CEncodingCore.palette,Physical.palette] using he
  · intro a d had
    rw [agrees b r h _ _ (small_ne r _ (by dsimp [rVertex];omega))
      (small_ne r _ (by dsimp [rVertex];omega))]
    change c (referenceMap b h (CommonCoordinates.Reference.right (layout p) a))
      (referenceMap b h (CommonCoordinates.Reference.right (layout p) d))=_
    rw [referenceMap_right,referenceMap_right]
    have he := CommonBlocks.right_edges b a d had
    have hm : PricingABD.ABGeometry.model (PricingABD.ABLayout.rightLarge (layout p)) false a d=
        R4333.k15Template false a d := by rfl
    simpa only [frame,physical_right,hm,UniformK61.Core.palette,CEncodingCore.palette,Physical.palette] using he
  · intro a d had
    by_cases ha : a=r.castSucc
    · subst a
      have hd := marked_ne r d had.symm
      change completed b r h (UUE.omitted r).castSucc (qVertex d)=_
      rw [missing_edge b r h _ hd]
      simp [incident,qVertex,
        UniformK61.Core.palette,CEncodingCore.palette,Physical.palette]
    by_cases hd : d=r.castSucc
    · subst d
      rw [(completed b r h).color_symm]
      change completed b r h (UUE.omitted r).castSucc (qVertex a)=_
      rw [missing_edge b r h _ (marked_ne r a ha)]
      simp [incident,qVertex,
        (R4333.k16Template q).color_symm r.castSucc a,
        UniformK61.Core.palette,CEncodingCore.palette,Physical.palette]
    · rw [agrees b r h _ _ (marked_ne r a ha) (marked_ne r d hd)]
      obtain ⟨a',ha'⟩ := CommonCoordinates.marked_preimage (layout p) (some r) a (marked_ne r a ha)
      obtain ⟨d',hd'⟩ := CommonCoordinates.marked_preimage (layout p) (some r) d (marked_ne r d hd)
      have had' : a'≠d' := by intro he;apply had;rw [←ha',←hd',he]
      change c (referenceMap b h (CommonCoordinates.Reference.marked (layout p) a))
        (referenceMap b h (CommonCoordinates.Reference.marked (layout p) d))=_
      rw [←ha',←hd',referenceMap_marked,referenceMap_marked,h.marked.map_color a' d' had']
      have hf (k : Fin 3) : PhysicalHelpers.foreign 3 k=PricingABD.ABGeometry.foreign 3 k := by
        fin_cases k <;> rfl
      rw [hf]
      rfl

#print axioms static
#print axioms restriction_good
end UniformK60.UUReferenceE
