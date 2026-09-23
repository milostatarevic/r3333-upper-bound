import PricingIntegration.PhysicalTypeTransport
import PricingIntegration.BSupportedBlocks

set_option autoImplicit false
namespace PricingIntegration.ABTypeOwner
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open Ramsey61.CPhysicalNormalization PricingIntegration.FixedPhysicalNeighborhood
open PricingIntegration.ABDRootPalette PricingIntegration.BActualFrame
open PricingIntegration.PhysicalTypeTransport

def slot (i : Fin 3) : Color := ⟨i.val+1,by omega⟩
def liftCode (code : Fin 6) : Fin 24 := ⟨code.val,by omega⟩
noncomputable def globalPalette (code : Fin 6) : FourColor ≃ FourColor :=
  paletteEquiv.symm.trans ((permEquiv (liftCode code)).trans paletteEquiv)

theorem globalPalette_apply (code : Fin 6) (q : Color) :
    globalPalette code (palette q)=palette (permEquiv (liftCode code) q) := by
  change paletteEquiv (permEquiv (liftCode code) (paletteEquiv.symm (paletteEquiv q)))=_
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem globalPalette_zero (code : Fin 6) : globalPalette code (palette 0)=palette 0 := by
  rw [globalPalette_apply];fin_cases code <;> rfl
@[simp] theorem globalPalette_slot (code : Fin 6) (i : Fin 3) :
    globalPalette code (palette (slot i))=palette (slot (R4333.criticalPaletteColorEquiv code i)) := by
  rw [globalPalette_apply];fin_cases code <;> fin_cases i <;> rfl

/-- Exact4A and6B canonical type owners, using only permutations of equal-sized
critical root cells. The low cell is fixed. -/
theorem A_owner_table (t : Fin 3 → Bool) :
    ∃ code : Fin 6,let s := fun i => t (R4333.criticalPaletteColorEquiv code i)
      (s 0=false ∨ s 1=true) ∧ (s 1=false ∨ s 2=true) := by
  revert t;decide

theorem B_owner_table (t : Fin 3 → Bool) :
    ∃ code : Fin 6,R4333.criticalPaletteColorEquiv code 0=0 ∧
      (t (R4333.criticalPaletteColorEquiv code 1)=false ∨ t (R4333.criticalPaletteColorEquiv code 2)=true) := by
  revert t;decide

/-- Allthree actualA cells with complete same-host fixed-palette maps. -/
structure ABlocks (c : Host) (r : Vertex) where
  types : Fin 3 → Bool
  cell : ∀ i,PhysicalNeighborhoodMap c r (palette (slot i)) (R4333.k16Template (types i))
  palettes : ∀ i,(cell i).colors=foreignEquiv (slot i)

theorem ordered_A_blocks (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : ∀ q : Color,colorDegree c (palette q) r=shape 0 q) :
    Nonempty (ABlocks c r) := by
  classical
  have hs : ∀ i : Fin 3,colorDegree c (palette (slot i)) r=16 := by
    intro i;rw [hd];fin_cases i <;> rfl
  have hh : ∀ i : Fin 3,∃t : Bool,∃m : PhysicalNeighborhoodMap c r (palette (slot i)) (R4333.k16Template t),m.colors=foreignEquiv (slot i) :=
    fun i => physical_k16_fixed_palette c hc r _ (hs i) (foreignEquiv (slot i))
  choose types cells hp using hh
  exact ⟨⟨types,cells,hp⟩⟩

theorem ABlocks.reorder {c : Host} {r : Vertex} (b : ABlocks c r) (code : Fin 6) :
    ∃ n : ABlocks (relabel c (Equiv.refl _) (globalPalette code)) r,
      ∀ i,n.types i=b.types (R4333.criticalPaletteColorEquiv code i) := by
  classical
  let τ := R4333.criticalPaletteColorEquiv code
  let σ := globalPalette code
  let d := relabel c (Equiv.refl _) σ
  have hmap (i : Fin 3) : PhysicalNeighborhoodMap c r (σ (palette (slot i))) (R4333.k16Template (b.types (τ i))) := by
    rw [globalPalette_slot];exact b.cell (τ i)
  have hh : ∀ i : Fin 3,∃m : PhysicalNeighborhoodMap d r (palette (slot i)) (R4333.k16Template (b.types (τ i))),m.colors=foreignEquiv (slot i) := by
    intro i
    exact k16_repalette (physical_relabel σ (palette (slot i)) (hmap i)) (foreignEquiv (slot i))
  choose cells hp using hh
  exact ⟨⟨fun i=>b.types (τ i),cells,hp⟩,fun i=>rfl⟩

theorem ordered_A_native_owner (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : ∀ q : Color,colorDegree c (palette q) r=shape 0 q)
    (hh : 48≤H c r) :
    ∃ code : Fin 6,
      let d := relabel c (Equiv.refl _) (globalPalette code)
      NoMonochromaticTriangle d ∧ H d r=H c r ∧ W d r=W c r ∧
      (∀ q : Color,colorDegree d (palette q) r=shape 0 q) ∧
      ∃ b : ABlocks d r,(b.types 0=false ∨ b.types 1=true) ∧ (b.types 1=false ∨ b.types 2=true) ∧
      ∃ m : PhysicalNeighborhoodMap d r (palette 3) (R4333.k16Template (b.types 2)),
        m.colors=foreignEquiv 3 ∧ 15≤colorDegree d (palette 3) (m.vertex 15) := by
  obtain ⟨b⟩ := ordered_A_blocks c hc r hd
  obtain ⟨code,horder⟩ := A_owner_table b.types
  obtain ⟨n,hn⟩ := b.reorder code
  let d := relabel c (Equiv.refl _) (globalPalette code)
  have good := relabel_noMono c hc (Equiv.refl _) (globalPalette code)
  have hH : H d r=H c r := relabel_H c _ _ _
  have hW : W d r=W c r := relabel_W c _ _ _
  have hdegree : ∀q : Color,colorDegree d (palette q) r=shape 0 q := by
    intro q
    simp only [d,relabel_degree,globalPalette_apply,Equiv.refl_apply]
    rw [hd]
    fin_cases q
    all_goals fin_cases code <;> rfl
  have hhigh : 46≤H d r := by rw [hH];omega
  obtain ⟨mark,hm,hmark,_⟩ := supplied_ABD_has_attaching_mark d good r (palette 3) (hdegree 3) hhigh
  obtain ⟨m,hpal,hmarked⟩ := k16_remark (n.cell 2) mark hm
  refine ⟨code,good,hH,hW,hdegree,n,?_,?_,m,?_,?_⟩
  · simpa only [hn] using horder.1
  · simpa only [hn] using horder.2
  · exact hpal.trans (n.palettes 2)
  · rw [hmarked];exact hmark

#print axioms ordered_A_native_owner
end PricingIntegration.ABTypeOwner
