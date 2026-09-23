import R4333Lean.CanonicalHighOwnTransport61
import R4333Lean.NormalizedCanonicalAttaching61
import R4333Lean.ProfileDRowExtensionConstruction
import R4333Lean.ProfileDHighOwnFiveSupportC5Formula
import Ramsey61.ABDExtraction
import Ramsey61.CEncodingCore
import Ramsey61.ClassificationAdapter

namespace PricingG.DHostAdapter
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open R4333.SingleRootStarCNF R4333.SingleRootStarWitness61
open R4333.CanonicalStarOwnColorDegree R4333.CanonicalHighOwnTransport61

abbrev DProfile := R4333.SingleRootStarCNF.Profile.p14_15_15_16

def OrderedD (c : Host) (r : Vertex) : Prop :=
  ∀ q : Color, colorDegree c (palette q) r = (![14,15,15,16] : Fin 4 → Nat) q

/-- The specified physical D root enters the old canonical mathematics.
The palette is the identity here: no different root is selected. -/
noncomputable def orderedReduction (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : OrderedD c r) : R4333.SingleRootStarReduction61 (toLegacy c) hc where
  root := r
  palette := Equiv.refl _
  profile := .fourteenFifteenFifteenSixteen
  sixteenColor := palette 3
  degreeProfile := by
    change (colorDegree c (palette 0) r,colorDegree c (palette 1) r,
      colorDegree c (palette 2) r,colorDegree c (palette 3) r) = (14,15,15,16)
    rw [hd 0,hd 1,hd 2,hd 3]
    rfl
  sixteenDegree := hd 3
  partition := R4333.rootColorNeighborhoodPartition _ r
  activeCompletion q h := Classical.choice
    (R4333.exists_sharedCriticalCompletion_of_degree _ _ q r h)

@[simp] theorem orderedReduction_profile (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : OrderedD c r) : cnfProfile (orderedReduction c hc r hd).profile = DProfile := rfl

noncomputable def orderedStar (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : OrderedD c r) : CanonicalStarWitness DProfile :=
  canonicalStarWitnessOfReduction (orderedReduction c hc r hd)

theorem extension_endpoint_degree (w : CanonicalStarWitness DProfile) (i : Fin 16) :
    R4333.colorDegree
      (R4333.ProfileDRowSupportBounds61.fullJoinedColoring (R4333.ProfileDRowExtension.extensionOfStar w))
      (3 : Fin 4) (.inr (R4333.ProfileDTripleJoinReduction.blockVertex 2 i.val)) =
    R4333.colorDegree w.coloring (3 : Fin 4) (R4333.SingleRootStarCNF.blockVertex DProfile 3 i.val) := by
  have he : R4333.ProfileDRowSupportBounds61.fullJoinedColoring (R4333.ProfileDRowExtension.extensionOfStar w) =
      R4333.relabelVertices w.coloring R4333.ProfileDRowExtensionConstruction.splitEquiv := by
    change R4333.ColoringJoinRows.joinColoring
      (R4333.ProfileDRowExtension.insideColoring w) (R4333.ProfileDTripleJoinReduction.tailColoring w)
      (R4333.ProfileDRowExtension.crossRows w) = _
    rw [R4333.ProfileDRowExtension.joinedColoring_eq_pullback]
    rfl
  rw [he,R4333.colorDegree_relabelVertices,R4333.ProfileDRowExtensionConstruction.splitEquiv_apply]
  change R4333.colorDegree w.coloring 3
    (R4333.ProfileDTripleJoinReduction.tailEmbedding (R4333.ProfileDTripleJoinReduction.blockVertex 2 i.val)) = _
  rw [R4333.ProfileDTripleJoinReduction.tailEmbedding_blockVertex 2 i.val i.isLt]
  rfl

/-- H≥46 supplies a genuinely high marked vertex in the specified K16
block, then transports that very vertex into canonical star coordinates. -/
theorem orderedD_has_high_last_block (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : OrderedD c r) (hh : 46 ≤ H c r) :
    ∃ i : Fin 16, 14 ≤ R4333.colorDegree (orderedStar c hc r hd).coloring
      (3 : Fin 4) (R4333.SingleRootStarCNF.blockVertex DProfile 3 i.val) := by
  classical
  obtain ⟨x,hxr,hx,_⟩ := Ramsey61.supplied_ABD_has_attaching_mark c hc r (palette 3) (hd 3) hh
  let data := orderedReduction c hc r hd
  have hx' : x ∈ R4333.colorNeighborhood (normalizedHost data) (indexedRootColor 3) data.root := hxr
  let xv : R4333.NeighborhoodVertex (normalizedHost data) (indexedRootColor 3) data.root := ⟨x,hx'⟩
  let i : Fin 16 := (blockLocalEquiv data 3).symm xv
  let z := R4333.SingleRootStarCNF.blockVertex DProfile 3 i.val
  have hz : hostRelabelVertex data z = x := by
    change (hostRelabelEquiv data (R4333.SingleRootStarCNF.blockVertex DProfile 3 i.val)).val = x
    exact (hostRelabelEquiv_blockVertex_val data 3 i.val i.isLt).trans
      (congrArg Subtype.val ((blockLocalEquiv data 3).apply_symm_apply xv))
  have hb : vertexBlock DProfile z = 3 := by
    change ((blockPositionEquiv DProfile) (R4333.SingleRootStarCNF.blockVertex DProfile 3 i.val)).1 = 3
    exact congrArg (fun t : BlockPosition DProfile => t.1)
      (blockPositionEquiv_blockVertex DProfile (3 : Fin 4) i.val i.isLt)
  have hdegree := canonical_own_degree_add_one_eq_normalized data z
  change R4333.colorDegree (orderedStar c hc r hd).coloring (vertexBlock DProfile z) z + 1 =
    R4333.colorDegree (normalizedHost data)
      (normalizedHost data data.root (hostRelabelVertex data z)) (hostRelabelVertex data z) at hdegree
  rw [hb,hz] at hdegree
  have hcolor : normalizedHost data data.root x = palette 3 :=
    ((mem_colorNeighborhood _ _ _ _).mp hxr).2
  rw [hcolor] at hdegree
  change R4333.colorDegree (orderedStar c hc r hd).coloring 3 z + 1 = colorDegree c (palette 3) x at hdegree
  refine ⟨i,?_⟩
  change 14 ≤ R4333.colorDegree (orderedStar c hc r hd).coloring 3 z
  omega

/-- Every selected ordered D root enters the actual old four/five support
split for its own physical K16 mark. No finite refutation is assumed. -/
theorem orderedD_supplies_high_row_split (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : OrderedD c r) (hh : 46 ≤ H c r) :
    ∃ kind : R4333.ProfileDTripleJoinReduction.Kind,
      Nonempty (R4333.ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension kind) ∨
      Nonempty (R4333.ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension kind) := by
  obtain ⟨i,hi⟩ := orderedD_has_high_last_block c hc r hd hh
  let w := orderedStar c hc r hd
  let ext := R4333.ProfileDRowExtension.extensionOfStar w
  have he : 14 ≤ R4333.colorDegree (R4333.ProfileDRowSupportBounds61.fullJoinedColoring ext)
      (R4333.ProfileDColumnOwnColorIncidence61.blockRootColor 2)
      (.inr (R4333.ProfileDTripleJoinReduction.blockVertex 2 i.val)) := by
    change 14 ≤ R4333.colorDegree
      (R4333.ProfileDRowSupportBounds61.fullJoinedColoring (R4333.ProfileDRowExtension.extensionOfStar w))
      (3 : Fin 4) (.inr (R4333.ProfileDTripleJoinReduction.blockVertex 2 i.val))
    rw [extension_endpoint_degree w i]
    exact hi
  refine ⟨R4333.ProfileDTripleJoinReduction.kindOfWitness w,?_⟩
  rcases R4333.ProfileDHighOwnFiveRowSplit61.exists_highOwnFiveRow_split ext 2 i he with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

#print axioms orderedD_has_high_last_block
#print axioms orderedD_supplies_high_row_split
end PricingG.DHostAdapter
