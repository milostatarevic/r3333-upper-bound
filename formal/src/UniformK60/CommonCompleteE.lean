import UniformK60.CommonCompleteD
import UniformK60.UUESource

set_option autoImplicit false
namespace UniformK60.CommonCompleteE
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonCompletion
open UniformK60.ABDEOwners UniformK60.ABDEEntrance UniformK60.ABDERootPalette
open UniformK60.PhysicalTypeTransport UniformK60.PhysicalHelpers
open UniformK60.ClassificationMarkedOmission
open UniformK60.UUPhysicalCover UniformK60.UUCoordinates
open PricingABD.ABLayout PricingABD.ABGeometry

/-- Every E ticket violation reaches one of the exact frozen231168 cases.
The mixed and foreign-U/U branches use the same actual marked15 cell. -/
theorem actual_E_cover (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=45) (hh : 45≤H c r) :
    ∃ k : EFormula.Case,∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (EFormula.formula k) := by
  obtain ⟨σ,good,_,hd,a,_,five,b,hroot,hcase⟩ :=
    CommonCover.actual_E_cover_or_UU c hc r hw hh
  rcases hcase with ⟨hleft,hright⟩ | hdone
  · let d := relabel c (Equiv.refl _) σ
    let b0 := CommonCompleteD.asUU b hleft hright
    obtain ⟨p,z,hzroot,_,hl,hr,perm,i,hmat⟩ :=
      actual_UU_matrix (a.types 2) b0 good
    have hz : z.root=r := hzroot.trans hroot
    have hm : z.mark ∈ colorNeighborhood d (palette 3) r := by
      simpa only [hz] using z.mark_mem
    obtain ⟨k,_,n,hn,hmark⟩ := physical_marked_omission (a.cell 2) z.mark hm
    have hpal : n.colors=foreignEquiv 3 := hn.trans (a.palettes 2)
    let mb := changeRoot (ofOmitted n hpal) z.root hz
    have hmark' : mb.vertex (markIndex (some k))=z.mark := by
      change n.vertex (survivingIndex k 14)=z.mark
      have he : survivingIndex k 14=markPosition k := by
        apply Subtype.ext
        exact markedPosition_mark (some k)
      rw [he]
      exact hmark
    let completion : Completion (reorderFree z (freePermutation p perm)) (some k) :=
      { marked := mb
        mark_eq := hmark'
        low_degree := by
          change colorDegree d (palette 0) z.root=14
          rw [hz]
          exact hd 0 }
    exact UUESource.exact_E_from_catalogue (a.types 2) p z good hl hr perm i hmat k completion
  · exact hdone

#print axioms actual_E_cover
end UniformK60.CommonCompleteE
