import UniformK60.ClassificationFixedPalette

/-! Explicit color-preserving maps for the three U-minus and nine T-minus
marked-vertex orbits. The finite maps are checked by ordinary kernel decision. -/
set_option autoImplicit false
namespace UniformK60.ClassificationMarks
open Ramsey61 Finset UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette

def markRepresentatives (twisted : Bool) : List (Fin 15) :=
  if twisted then [0,1,2,4,5,6,7,9,12] else [0,1,2]

def markRepresentative (twisted : Bool) : Fin 15 → Fin 15 :=
  if twisted then ![0,1,2,0,4,5,6,7,2,9,9,1,12,4,7] else ![0,1,2,0,2,0,1,0,2,1,1,1,2,2,0]

def markToRepresentative (twisted : Bool) (mark : Fin 15) : Fin 15 → Fin 15 :=
  if twisted then (![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7]] : Fin 15 → Fin 15 → Fin 15) mark
  else (![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7],![7,6,4,5,2,3,1,0,8,9,11,10,13,12,14],![5,9,2,14,12,0,11,7,13,1,10,6,4,8,3],![5,10,8,7,12,3,1,14,4,11,9,6,13,2,0],![3,9,4,14,13,7,10,0,12,6,11,1,2,8,5],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7],![5,9,2,14,12,0,11,7,13,1,10,6,4,8,3],![0,10,13,7,4,14,9,3,12,6,1,11,8,2,5],![3,9,4,14,13,7,10,0,12,6,11,1,2,8,5],![3,9,4,14,13,7,10,0,12,6,11,1,2,8,5],![0,10,13,7,4,14,9,3,12,6,1,11,8,2,5],![5,10,8,7,12,3,1,14,4,11,9,6,13,2,0]] : Fin 15 → Fin 15 → Fin 15) mark

set_option maxRecDepth 100000 in
theorem markToRepresentative_bijective : ∀ t i, Function.Bijective (markToRepresentative t i) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem markToRepresentative_preserves : ∀ t i a b, a ≠ b →
    R4333.k15Template t (markToRepresentative t i a) (markToRepresentative t i b) =
      R4333.k15Template t a b := by
  decide

theorem markRepresentative_mem : ∀ t i, markRepresentative t i ∈ markRepresentatives t := by
  decide

theorem markToRepresentative_mark : ∀ t i,
    markToRepresentative t i i = markRepresentative t i := by
  decide

theorem markRepresentatives_length :
    (markRepresentatives false).length = 3 ∧ (markRepresentatives true).length = 9 := by
  decide

noncomputable def markEquiv (t : Bool) (i : Fin 15) : Fin 15 ≃ Fin 15 :=
  Equiv.ofBijective (markToRepresentative t i) (markToRepresentative_bijective t i)

/-- A chosen physical mark can occupy one of the retained3/9positions in its
actual15-vertex template, without changing any physical palette or vertex. -/
theorem physical_k15_marked_fixed_palette (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (hd : colorDegree c q r = 15)
    (mark : Fin 60) (hmark : mark ∈ colorNeighborhood c q r)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ t : Bool, ∃ i ∈ markRepresentatives t,
      ∃ m : PhysicalNeighborhoodMap c r q (R4333.k15Template t),
        m.colors = pal ∧ m.vertex i = mark := by
  obtain ⟨t, m, hp⟩ := physical_k15_fixed_palette c hc r q hd pal
  obtain ⟨i, hi⟩ := m.covers_neighborhood mark hmark
  let e := markEquiv t i
  have hroot : e i = markRepresentative t i := markToRepresentative_mark t i
  have he : ∀ a b, a ≠ b →
      modelInPalette m pal (e.symm a) (e.symm b) = R4333.k15Template t a b := by
    intro a b hab
    change pal.symm (m.colors (R4333.k15Template t (e.symm a) (e.symm b))) = _
    rw [hp, Equiv.symm_apply_apply]
    have h := markToRepresentative_preserves t i (e.symm a) (e.symm b) (e.symm.injective.ne hab)
    change R4333.k15Template t (e (e.symm a)) (e (e.symm b)) = _ at h
    simpa only [Equiv.apply_symm_apply] using h.symm
  refine ⟨t, markRepresentative t i, markRepresentative_mem t i,
    mapOfNormalization m pal e.symm he, rfl, ?_⟩
  change m.vertex (e.symm (markRepresentative t i)) = mark
  rw [← hroot, Equiv.symm_apply_apply, hi]

#print axioms markToRepresentative_preserves
#print axioms physical_k15_marked_fixed_palette
end UniformK60.ClassificationMarks
