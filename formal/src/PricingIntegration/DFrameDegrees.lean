import PricingIntegration.DFrameRows
import PricingABD.ABNumericBounds

set_option autoImplicit false
namespace PricingIntegration.DFrameDegrees
open Ramsey61 Finset
open Ramsey61.CEncodingCore (palette palette_injective)
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry PricingABD.ABPhysicalBounds
open PricingIntegration.DFrameColoring PricingIntegration.DFrameRows

def tailEmbedding {c : Host} {five : Bool} (f : Frame c (layout five)) : Fin 46 ↪ Fin 61 :=
  ⟨fun x=>f.vertex (tailIndex five x),f.vertex.injective.comp (tailIndex_injective five)⟩

theorem free_tail_ne {c : Host} {five : Bool} (f : Frame c (layout five))
    (a : Fin (freeSize (layout five))) (x : Fin 46) : tailEmbedding f x≠f.vertex (ABLayout.free (layout five) a) := by
  apply f.vertex.injective.ne
  intro he
  have hv:=congrArg Fin.val he
  change freeSize (layout five)+x.val=a.val at hv
  have ha:=a.isLt
  omega

theorem rows_eq_iff {c : Host} {five : Bool} (f : Frame c (layout five))
    (a : Fin (freeSize (layout five))) (x : Fin 46) (q : Fin 4) :
    rows f a x=q ↔ c (f.vertex (ABLayout.free (layout five) a)) (tailEmbedding f x)=palette q := by
  exact Equiv.symm_apply_eq paletteEquiv

theorem rowSupport_card {c : Host} {five : Bool} (f : Frame c (layout five))
    (a : Fin (freeSize (layout five))) (q : Fin 4) :
    (R4333.ColoringJoinRows.rowColorSupport (rows f a) q).card=
      tailCount f (ABLayout.free (layout five) a) q := by
  classical
  rw [←card_image_of_injective _ (tailEmbedding f).injective]
  unfold tailCount
  congr 1
  ext y
  simp only [mem_image,R4333.ColoringJoinRows.mem_rowColorSupport,mem_inter]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨free_tail_ne f a x,(rows_eq_iff f a x q).mp hx⟩,
      mem_image.mpr ⟨x,mem_univ _,rfl⟩⟩
  · rintro ⟨hn,ht⟩
    obtain ⟨x,_,rfl⟩:=mem_image.mp ht
    exact ⟨x,(rows_eq_iff f a x q).mpr ((mem_colorNeighborhood _ _ _ _).mp hn).2,rfl⟩

theorem tailColor_eq_iff {c : Host} {five : Bool} (f : Frame c (layout five))
    (u v : Fin 46) (q : Fin 4) :
    tailColoring f u v=q ↔ c (tailEmbedding f u) (tailEmbedding f v)=palette q := by
  exact Equiv.symm_apply_eq paletteEquiv

theorem tailDegree_card {c : Host} {five : Bool} (f : Frame c (layout five))
    (u : Fin 46) (q : Fin 4) :
    R4333.colorDegree (tailColoring f) q u=tailCount f (tailIndex five u) q := by
  classical
  unfold R4333.colorDegree
  rw [←card_image_of_injective _ (tailEmbedding f).injective]
  unfold tailCount
  congr 1
  ext y
  simp only [mem_image,R4333.mem_colorNeighborhood,mem_inter]
  constructor
  · rintro ⟨x,⟨hne,hcol⟩,rfl⟩
    exact ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨(tailEmbedding f).injective.ne hne,(tailColor_eq_iff f u x q).mp hcol⟩,
      mem_image.mpr ⟨x,mem_univ _,rfl⟩⟩
  · rintro ⟨hn,ht⟩
    obtain ⟨x,_,rfl⟩:=mem_image.mp ht
    obtain ⟨hne,hcol⟩:=(mem_colorNeighborhood _ _ _ _).mp hn
    exact ⟨x,⟨fun he=>hne (congrArg (tailEmbedding f) he),(tailColor_eq_iff f u x q).mpr hcol⟩,rfl⟩

noncomputable def degreeFloored {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension (kind t) where
  toFiveExtension:=fiveExtension f t hg hc
  zeroSupportLower:=by
    intro a
    change 11≤(R4333.ColoringJoinRows.rowColorSupport (rows f a) 0).card
    rw [rowSupport_card]
    exact (ABNumericBounds.free_bounds f hc a 1 (by decide)).1
  zeroSupportUpper:=by
    intro a
    change (R4333.ColoringJoinRows.rowColorSupport (rows f a) 0).card≤15
    rw [rowSupport_card]
    exact (ABNumericBounds.free_bounds f hc a 1 (by decide)).2.1
  nonzeroSupportLower:=by
    intro a q hq
    change 7≤(R4333.ColoringJoinRows.rowColorSupport (rows f a) q).card
    rw [rowSupport_card]
    exact (ABNumericBounds.free_bounds f hc a q hq).2.2.1
  nonzeroSupportUpper:=by
    intro a q hq
    change (R4333.ColoringJoinRows.rowColorSupport (rows f a) q).card≤13
    rw [rowSupport_card]
    exact (ABNumericBounds.free_bounds f hc a q hq).2.2.2.1

theorem marked_tail_bounds {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    9≤tailCount f (mark (layout true)) 3 ∧ tailCount f (mark (layout true)) 3≤10 := by
  have hlow := ABNumericBounds.high_tail_proxy f hc (45 : Fin 46) f.marked_high
  have hlower : 9≤tailCount f (mark (layout true)) 3 := hlow
  have hsub : support f ⊆ colorNeighborhood c (palette 3) (f.vertex (mark (layout true))) ∩
      colorNeighborhood c (palette 0) f.root := by
    intro v hv
    have hfree:=support_subset f hv
    obtain ⟨a,_,rfl⟩:=mem_image.mp hv
    have hne : f.vertex (ABLayout.free (layout true) a)≠f.vertex (mark (layout true)) := by
      exact (free_tail_ne f a (45 : Fin 46)).symm
    exact mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨hne,hg.mark_free a⟩,hfree⟩
  have hcard:=card_le_card hsub
  rw [support_card] at hcard
  change 5≤lowCellDegree c f.root (palette 0) (f.vertex (mark (layout true))) (palette 3) at hcard
  have hroot : f.root ∈ colorNeighborhood c (palette 3) (f.vertex (mark (layout true))) := by
    apply (mem_colorNeighborhood _ _ _ _).mpr
    refine ⟨(f.ne_root _).symm,?_⟩
    rw [c.color_symm,f.spokes]
    rfl
  have hp:=tail_low_root_partition c f.root (palette 0) (f.vertex (mark (layout true))) (palette 3)
  rw [if_pos hroot] at hp
  have hc16:=fourColor_colorDegree_le_sixteen c hc (palette 3) (f.vertex (mark (layout true)))
  rw [tailCount_eq] at hlower ⊢
  exact ⟨hlower,by omega⟩

#print axioms degreeFloored
#print axioms marked_tail_bounds
end PricingIntegration.DFrameDegrees
