import PricingIntegration.DFrameColoring
import PricingABD.ABPhysicalBounds

set_option autoImplicit false
namespace PricingIntegration.DFrameRows
open Ramsey61
open Ramsey61.CEncodingCore (palette)
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.DFrameColoring

def fullIndex (five : Bool) : Fin (freeSize (layout five)) ⊕ Fin 46 → Fin (vertexCount (layout five))
  | .inl u=>ABLayout.free (layout five) u
  | .inr v=>tailIndex five v

theorem fullIndex_injective (five : Bool) : Function.Injective (fullIndex five) := by
  intro x y h
  cases x with
  | inl x=>
    cases y with
    | inl y=> exact congrArg Sum.inl (free_injective (layout five) h)
    | inr y=>
      have hv:=congrArg Fin.val h
      change x.val=freeSize (layout five)+y.val at hv
      have hx:=x.isLt
      omega
  | inr x=>
    cases y with
    | inl y=>
      have hv:=congrArg Fin.val h
      change freeSize (layout five)+x.val=y.val at hv
      have hy:=y.isLt
      omega
    | inr y=> exact congrArg Sum.inr (tailIndex_injective five h)

noncomputable def inside {c : Host} {five : Bool} (f : Frame c (layout five)) :=
  R4333.pullbackColoring (coloring f) (ABLayout.free (layout five))

noncomputable def rows {c : Host} {five : Bool} (f : Frame c (layout five))
    (u : Fin (freeSize (layout five))) (v : Fin 46) : Fin 4 :=
  coloring f (ABLayout.free (layout five) u) (tailIndex five v)

theorem joined_eq {c : Host} {five : Bool} (f : Frame c (layout five)) :
    R4333.ColoringJoinRows.joinColoring (inside f) (tailColoring f) (rows f)=
      R4333.pullbackColoring (coloring f) (fullIndex five) := by
  ext u v
  cases u <;> cases v <;>
    simp [inside,tailColoring,rows,fullIndex,R4333.ColoringJoinRows.joinColoring,
      R4333.pullbackColoring,(coloring f).color_symm]

theorem joined_good {c : Host} {five : Bool} (f : Frame c (layout five))
    (hc : NoMonochromaticTriangle c) :
    R4333.NoMonochromaticTriangle (R4333.ColoringJoinRows.joinColoring (inside f) (tailColoring f) (rows f)) := by
  rw [joined_eq]
  exact R4333.noMono_pullback (coloring f) (fullIndex five) (fullIndex_injective five) (coloring_good f hc)

theorem inside_forbidden {c : Host} {five : Bool} (f : Frame c (layout five))
    (hc : NoMonochromaticTriangle c) (u v : Fin (freeSize (layout five))) (hne : u≠v) :
    inside f u v≠0 := by
  intro h
  change paletteEquiv.symm (c (f.vertex (ABLayout.free (layout five) u))
    (f.vertex (ABLayout.free (layout five) v)))=0 at h
  have he : c (f.vertex (ABLayout.free (layout five) u))
      (f.vertex (ABLayout.free (layout five) v))=palette 0 := (Equiv.symm_apply_eq paletteEquiv).mp h
  exact neighborhood_avoids_own_color c hc (ABPhysicalBounds.free_mem f u) (ABPhysicalBounds.free_mem f v)
    (f.vertex.injective.ne ((free_injective (layout five)).ne hne)) he

noncomputable def fourExtension {c : Host} (f : Frame c (layout false))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDFourRowBoundary.FourExtension (kind t) where
  tail:=witness f t hg hc
  inside:=inside f
  rows:=rows f
  insideNoMono:=(R4333.ColoringJoinRows.noMono_joinColoring_iff _ _ _).mp (joined_good f hc) |>.1
  insideRootForbidden:=inside_forbidden f hc
  rowsAdmissible:=(R4333.ColoringJoinRows.noMono_joinColoring_iff _ _ _).mp (joined_good f hc) |>.2.2.1
  rowsPairCompatible:=(R4333.ColoringJoinRows.noMono_joinColoring_iff _ _ _).mp (joined_good f hc) |>.2.2.2

noncomputable def fiveExtension {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDHighOwnFiveRowSplit61.FiveExtension (kind t) where
  tail:=witness f t hg hc
  inside:=inside f
  rows:=rows f
  insideNoMono:=(R4333.ColoringJoinRows.noMono_joinColoring_iff _ _ _).mp (joined_good f hc) |>.1
  insideRootForbidden:=inside_forbidden f hc
  rowsAdmissible:=(R4333.ColoringJoinRows.noMono_joinColoring_iff _ _ _).mp (joined_good f hc) |>.2.2.1
  rowsPairCompatible:=(R4333.ColoringJoinRows.noMono_joinColoring_iff _ _ _).mp (joined_good f hc) |>.2.2.2

theorem fullIndex_split_four (v : Fin 50) :
    fullIndex false (R4333.ProfileDFourRowCNF.splitVertex v)=v := by
  by_cases hv : v.val<4
  · apply Fin.ext
    simp [R4333.ProfileDFourRowCNF.splitVertex,hv,fullIndex,ABLayout.free]
  · apply Fin.ext
    simp [R4333.ProfileDFourRowCNF.splitVertex,hv,fullIndex,tailIndex,ABLayout.tail,freeSize,layout]
    omega

theorem fullIndex_split_five (v : Fin 51) :
    fullIndex true (R4333.ProfileDHighOwnFiveSupportC5CNF.splitVertex v)=v := by
  by_cases hv : v.val<5
  · apply Fin.ext
    simp [R4333.ProfileDHighOwnFiveSupportC5CNF.splitVertex,hv,fullIndex,ABLayout.free]
  · apply Fin.ext
    simp [R4333.ProfileDHighOwnFiveSupportC5CNF.splitVertex,hv,fullIndex,tailIndex,ABLayout.tail,freeSize,layout]
    omega

theorem four_total_eq {c : Host} (f : Frame c (layout false))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDFourRowCNF.totalColoring (fourExtension f t hg hc)=coloring f := by
  ext u v
  apply congrArg Fin.val
  change (R4333.ColoringJoinRows.joinColoring (inside f) (tailColoring f) (rows f))
    (R4333.ProfileDFourRowCNF.splitVertex u) (R4333.ProfileDFourRowCNF.splitVertex v)=_
  rw [joined_eq]
  change coloring f (fullIndex false (R4333.ProfileDFourRowCNF.splitVertex u))
    (fullIndex false (R4333.ProfileDFourRowCNF.splitVertex v))=_
  rw [fullIndex_split_four,fullIndex_split_four]

theorem five_total_eq {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDHighOwnFiveSupportC5CNF.totalColoring (fiveExtension f t hg hc)=coloring f := by
  ext u v
  apply congrArg Fin.val
  change (R4333.ColoringJoinRows.joinColoring (inside f) (tailColoring f) (rows f))
    (R4333.ProfileDHighOwnFiveSupportC5CNF.splitVertex u) (R4333.ProfileDHighOwnFiveSupportC5CNF.splitVertex v)=_
  rw [joined_eq]
  change coloring f (fullIndex true (R4333.ProfileDHighOwnFiveSupportC5CNF.splitVertex u))
    (fullIndex true (R4333.ProfileDHighOwnFiveSupportC5CNF.splitVertex v))=_
  rw [fullIndex_split_five,fullIndex_split_five]

theorem four_base_satisfied {c : Host} (f : Frame c (layout false))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    (R4333.FiniteColorCNF.coloringValuation (coloring f)).satisfies_fmla (R4333.ProfileDFourRowCNF.fmla (kind t)) := by
  have h:=R4333.ProfileDFourRowCNF.fourExtension_satisfies_fmla (fourExtension f t hg hc)
  rw [four_total_eq] at h
  exact h

#print axioms four_base_satisfied
#print axioms fiveExtension
end PricingIntegration.DFrameRows
