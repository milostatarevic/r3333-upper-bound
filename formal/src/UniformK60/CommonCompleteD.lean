import UniformK60.CommonCover
import UniformK60.UUDSource

/-! Complete D by joining the common mixed-owner cover to the independently
checked679-leaf U/U cover. All geometry belongs to the actual60-vertex host. -/
set_option autoImplicit false
namespace UniformK60.CommonCompleteD
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonCompletion
open UniformK60.ABDEOwners UniformK60.ABDEEntrance UniformK60.ABDERootPalette
open UniformK60.PhysicalTypeTransport UniformK60.PhysicalHelpers
open UniformK60.UUPhysicalCover UniformK60.UUCoordinates
open PricingABD.ABLayout PricingABD.ABGeometry

noncomputable def asUU {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (hl : t.left=false) (hr : t.right=false) :
    Blocks c l ⟨false,false,t.marked⟩ where
  root := b.root
  mark := b.mark
  free := b.free
  left := by simpa only [hl] using b.left
  right := by simpa only [hr] using b.right
  mark_mem := b.mark_mem
  free_mem := b.free_mem
  left_palette := by rcases t with ⟨tl,tr,tm⟩;cases hl;exact b.left_palette
  right_palette := by rcases t with ⟨tl,tr,tm⟩;cases hr;exact b.right_palette
  marked_high := b.marked_high
  free_own := b.free_own
  free_exact := b.free_exact

/-- Every supplied D ticket violation satisfies one of the exact frozen
50,918 D formulas (within the shared A/B/D case type). -/
theorem actual_D_cover (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=46) (hh : 46≤H c r) :
    ∃ k : ABDFormula.Case,∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (ABDFormula.formula k) := by
  obtain ⟨σ,good,_,hd,a,_,five,b,hroot,hcase⟩ :=
    CommonCover.actual_D_cover_or_UU c hc r hw hh
  rcases hcase with ⟨hleft,hright⟩ | hdone
  · let d := relabel c (Equiv.refl _) σ
    let b0 := asUU b hleft hright
    obtain ⟨p,z,hzroot,_,hl,hr,perm,i,hmat⟩ :=
      actual_UU_matrix (a.types 2) b0 good
    have hz : z.root=r := hzroot.trans hroot
    have hm : z.mark ∈ colorNeighborhood d (palette 3) r := by
      simpa only [hz] using z.mark_mem
    obtain ⟨n,hn,hmark⟩ := k16_remark (a.cell 2) z.mark hm
    have hpal : n.colors=foreignEquiv 3 := hn.trans (a.palettes 2)
    let mb := changeRoot (ofFull n hpal) z.root hz
    let completion : Completion (reorderFree z (freePermutation p perm)) none :=
      { marked := mb
        mark_eq := hmark
        low_degree := by
          change colorDegree d (palette 0) z.root=13
          rw [hz]
          exact hd 0 }
    obtain ⟨j,v,hv⟩ := UUDSource.exact_D_from_catalogue (a.types 2) p z good
      hl hr perm i hmat completion
    exact ⟨.inr (a.types 2,j),v,hv⟩
  · exact hdone

#print axioms actual_D_cover
end UniformK60.CommonCompleteD
