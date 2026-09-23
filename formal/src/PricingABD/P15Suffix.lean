import PricingABD.P15Encoder

namespace PricingABD.P15Suffix
open Ramsey61 Ramsey61.CEncodingCore PricingABD.TTExchange PricingABD.P15Encoder
open R4333.FiniteColorCNF

/-- The suffix decoder sorts the actual physical pair before the sparse atom. -/
def physicalUnit (a b : Fin 50) (q : Fin 4) : Sat.Clause :=
  positiveUnit (min a.val b.val) (max a.val b.val) q

theorem physicalUnit_satisfied {c : Host} {t : Bool} (f : Frame c 4 t)
    (a b : Fin 50) (q : Fin 4)
    (h : c (physicalVertex f a) (physicalVertex f b) = palette q) :
    (coloringValuation (physicalColoring f)).satisfies (physicalUnit a b q) := by
  by_cases hab : a.val ≤ b.val
  · simpa [physicalUnit,min_eq_left hab,max_eq_right hab] using positiveUnit_satisfied f a b q h
  · have hba : b.val ≤ a.val := by omega
    have hh : c (physicalVertex f b) (physicalVertex f a) = palette q := by rw [c.color_symm];exact h
    simpa [physicalUnit,min_eq_right hba,max_eq_left hba] using positiveUnit_satisfied f b a q hh

/-- Exactly the91pairs read by the archived stage0 decoder, in canonical14-label order. -/
def suffix (placement : Fin 14 → Fin 50) (matrix : Fin 14 → Fin 14 → Fin 4) : Sat.Fmla :=
  (edges 14).map fun pair => physicalUnit (placement ⟨pair.1%14,by omega⟩)
    (placement ⟨pair.2%14,by omega⟩) (matrix ⟨pair.1%14,by omega⟩ ⟨pair.2%14,by omega⟩)

theorem suffix_length (placement : Fin 14 → Fin 50) (matrix : Fin 14 → Fin 14 → Fin 4) :
    (suffix placement matrix).length = 91 := by simp [suffix,List.length_map];decide

/-- Transport every observed edge of the same physical host to its exact signed unit. -/
theorem suffix_satisfied {c : Host} {t : Bool} (f : Frame c 4 t)
    (placement : Fin 14 → Fin 50) (matrix : Fin 14 → Fin 14 → Fin 4)
    (observed : ∀ a b, a ≠ b →
      c (physicalVertex f (placement a)) (physicalVertex f (placement b)) = palette (matrix a b)) :
    (coloringValuation (physicalColoring f)).satisfies_fmla (suffix placement matrix) := by
  constructor
  intro clause hcl
  simp only [suffix,List.mem_map] at hcl
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := hcl
  obtain ⟨ha,hb,hlt⟩ := mem_edges_bounds hab
  let u : Fin 14 := ⟨a,ha⟩
  let v : Fin 14 := ⟨b,hb⟩
  have h := physicalUnit_satisfied f (placement u) (placement v) _ (observed u v (Fin.ne_of_lt hlt))
  simpa only [u,v,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using h

/-- The matrix is read from the one actual retained coloring, rather than
assumed to have a compatible physical realization. -/
noncomputable def observedMatrix {c : Host} {t : Bool} (f : Frame c 4 t)
    (placement : Fin 14 → Fin 50) (a b : Fin 14) : Fin 4 :=
  physicalColoring f (placement a) (placement b)

theorem observedMatrix_edges {c : Host} {t : Bool} (f : Frame c 4 t)
    (placement : Fin 14 → Fin 50) (a b : Fin 14) :
    c (physicalVertex f (placement a)) (physicalVertex f (placement b)) =
      palette (observedMatrix f placement a b) := by
  exact (paletteEquiv.apply_symm_apply _).symm

/-- Complete forward semantics of the unchanged87311+91 sparse P15 leaf.
The finite600-word orbit cover is the separate task of identifying its observed
matrix with a retained representative after permitted physical block actions. -/
theorem frame_satisfies_observed_P15_leaf {c : Host} {t : Bool} (f : Frame c 4 t)
    (hc : NoMonochromaticTriangle c) (placement : Fin 14 ↪ Fin 50) :
    (coloringValuation (physicalColoring f)).satisfies_fmla
      (baseFmla t ++ suffix placement (observedMatrix f placement)) := by
  constructor
  intro clause hcl
  rcases List.mem_append.mp hcl with h | h
  · exact (frame_satisfies_exact_P15_base f hc).prop clause h
  · exact (suffix_satisfied f placement (observedMatrix f placement)
      (fun a b _ => observedMatrix_edges f placement a b)).prop clause h

#print axioms suffix_satisfied
#print axioms frame_satisfies_observed_P15_leaf
#check frame_satisfies_observed_P15_leaf
end PricingABD.P15Suffix
