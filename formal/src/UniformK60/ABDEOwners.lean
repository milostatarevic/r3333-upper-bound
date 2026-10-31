import UniformK60.ABDERootPalette
import UniformK60.PhysicalTypeTransport
import UniformK60.CommonEntrance
import PricingIntegration.ABTypeOwner

/-! Order only equal-sized critical cells. The same construction gives
four A owners, six B owners, six D owners, and four E owners. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace UniformK60.ABDEOwners
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette
open UniformK60.ClassificationGeometry UniformK60.PhysicalHelpers
open UniformK60.PhysicalTypeTransport UniformK60.ABDERootPalette
open PricingABD.ABGeometry (model)

abbrev slot := PricingIntegration.ABTypeOwner.slot
noncomputable abbrev globalPalette := PricingIntegration.ABTypeOwner.globalPalette
noncomputable abbrev slotPerm := R4333.criticalPaletteColorEquiv

def large (profile : Fin 4) : Fin 3 → Bool :=
  (![![true,true,true],![false,true,true],![false,false,true],![false,false,false]] :
    Fin 4 → Fin 3 → Bool) profile

def Ordered (profile : Fin 4) (t : Fin 3 → Bool) : Prop :=
  if profile=1 then t 1=false ∨ t 2=true
  else if profile=2 then t 0=false ∨ t 1=true
  else (t 0=false ∨ t 1=true) ∧ (t 1=false ∨ t 2=true)

instance orderedDecidable (p : Fin 4) (t : Fin 3 → Bool) : Decidable (Ordered p t) := by
  unfold Ordered
  infer_instance

@[simp] theorem global_zero (code : Fin 6) : globalPalette code (palette 0)=palette 0 :=
  PricingIntegration.ABTypeOwner.globalPalette_zero code

@[simp] theorem global_slot (code : Fin 6) (i : Fin 3) :
    globalPalette code (palette (slot i))=palette (slot (slotPerm code i)) :=
  PricingIntegration.ABTypeOwner.globalPalette_slot code i

theorem owner_table : ∀ (profile : Fin 4) (t : Fin 3 → Bool),
    ∃ code : Fin 6,
      (∀ i,large profile (slotPerm code i)=large profile i) ∧
      Ordered profile (fun i => t (slotPerm code i)) := by decide

theorem critical_size (profile : Fin 4) (i : Fin 3) :
    shape profile (slot i) = if large profile i then 16 else 15 := by
  fin_cases profile <;> fin_cases i <;> rfl

structure Cells (c : Host) (r : Vertex) (profile : Fin 4) where
  types : Fin 3 → Bool
  cell : ∀ i,PhysicalNeighborhoodMap c r (palette (slot i))
    (model (large profile i) (types i))
  palettes : ∀ i,(cell i).colors=foreignEquiv (slot i)

theorem cells_of_ordered (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (profile : Fin 4)
    (hd : ∀ q : Color,colorDegree c (palette q) r=shape profile q) :
    Nonempty (Cells c r profile) := by
  classical
  have hh : ∀ i : Fin 3,∃ t : Bool,
      ∃ m : PhysicalNeighborhoodMap c r (palette (slot i)) (model (large profile i) t),
        m.colors=foreignEquiv (slot i) := by
    intro i
    have hn := (hd (slot i)).trans (critical_size profile i)
    cases hlarge : large profile i
    · simp only [hlarge,Bool.false_eq_true,if_false] at hn
      exact physical_k15_fixed_palette c hc r _ hn (foreignEquiv (slot i))
    · simp only [hlarge,if_true] at hn
      exact physical_k16_fixed_palette c hc r _ hn (foreignEquiv (slot i))
  choose types maps hp using hh
  exact ⟨⟨types,maps,hp⟩⟩

theorem model_repalette {c : Host} {r : Vertex} {q : FourColor} (big t : Bool)
    (m : PhysicalNeighborhoodMap c r q (model big t))
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ z : PhysicalNeighborhoodMap c r q (model big t),z.colors=pal := by
  cases big
  · exact k15_repalette m pal
  · exact k16_repalette m pal

theorem Cells.reorder {c : Host} {r : Vertex} {profile : Fin 4}
    (b : Cells c r profile) (code : Fin 6)
    (hs : ∀ i,large profile (slotPerm code i)=large profile i) :
    ∃ z : Cells (relabel c (Equiv.refl _) (globalPalette code)) r profile,
      ∀ i,z.types i=b.types (slotPerm code i) := by
  classical
  let σ := globalPalette code
  let d := relabel c (Equiv.refl _) σ
  have hmap (i : Fin 3) : PhysicalNeighborhoodMap c r (σ (palette (slot i)))
      (model (large profile i) (b.types (slotPerm code i))) := by
    dsimp only [σ]
    rw [global_slot,← hs i]
    exact b.cell (slotPerm code i)
  have hh : ∀ i : Fin 3,
      ∃ m : PhysicalNeighborhoodMap d r (palette (slot i))
        (model (large profile i) (b.types (slotPerm code i))),
        m.colors=foreignEquiv (slot i) := by
    intro i
    exact model_repalette _ _ (physical_relabel σ _ (hmap i)) (foreignEquiv (slot i))
  choose maps hp using hh
  exact ⟨⟨fun i => b.types (slotPerm code i),maps,hp⟩,fun _ => rfl⟩

/-- One global palette change sorts the equal-size critical template types,
then a genuine sender is selected in the last critical cell. -/
theorem ordered_owner_with_mark (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (profile : Fin 4)
    (hd : ∀ q : Color,colorDegree c (palette q) r=shape profile q)
    (hh : mass profile≤H c r) :
    ∃ σ : FourColor ≃ FourColor,let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧
      (∀ q : Color,colorDegree d (palette q) r=shape profile q) ∧
      ∃ b : Cells d r profile,Ordered profile b.types ∧
      ∃ mark ∈ colorNeighborhood d (palette 3) r,
        15≤colorDegree d (palette 3) mark := by
  obtain ⟨b⟩ := cells_of_ordered c hc r profile hd
  obtain ⟨code,hs,ho⟩ := owner_table profile b.types
  obtain ⟨z,hz⟩ := b.reorder code hs
  let σ := globalPalette code
  let d := relabel c (Equiv.refl _) σ
  have good : NoMonochromaticTriangle d := relabel_noMono c hc _ _
  have hH : H d r=H c r := relabel_H c _ _ _
  have hsdegree (i : Fin 3) :
      colorDegree c (σ (palette (slot i))) r=shape profile (slot i) := by
    dsimp only [σ]
    rw [global_slot,hd,critical_size,hs]
    exact (critical_size profile i).symm
  have hdegree : ∀ q : Color,colorDegree d (palette q) r=shape profile q := by
    intro q
    dsimp only [d]
    rw [relabel_degree]
    simp only [Equiv.refl_apply]
    fin_cases q
    · change colorDegree c (globalPalette code (palette 0)) r=shape profile 0
      rw [global_zero,hd]
    · exact hsdegree 0
    · exact hsdegree 1
    · exact hsdegree 2
  have horder : Ordered profile z.types := by
    have hzfun : z.types=(fun i => b.types (slotPerm code i)) := funext hz
    rw [hzfun]
    exact ho
  refine ⟨σ,good,hH,hdegree,z,horder,?_⟩
  by_cases hp : profile=3
  · subst profile
    obtain ⟨mark,hm,high,_⟩ := supplied_E_has_attaching_mark d good r (palette 3)
      (hdegree 3) (by rw [hH];exact hh)
    exact ⟨mark,hm,high⟩
  · have hd3 : colorDegree d (palette 3) r=16 := by
      rw [hdegree];fin_cases profile <;> simp_all [shape]
    have ht : 46≤H d r := by
      rw [hH]
      fin_cases profile <;> simp_all [mass] <;> omega
    obtain ⟨mark,hm,high,_⟩ := supplied_ABD_has_attaching_mark d good r (palette 3) hd3 ht
    exact ⟨mark,hm,high⟩

#print axioms ordered_owner_with_mark
end UniformK60.ABDEOwners
