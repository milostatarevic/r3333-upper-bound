import UniformK60.ReferenceSource
import UniformK61.UnitTransport

/-!
One omitted reference position may be assigned arbitrary incident colors.
The resulting reference coloring is not asserted to be triangle-free.
Only its restriction, which is the actual sixty-vertex coloring, is used.
-/

set_option autoImplicit false
namespace UniformK60.ReferenceExtension
open Ramsey61 UniformK60.Physical UniformK60.UnitRestriction

def extend (c : Core.Coloring) (d : Omission) (incident : Vertex → FourColor) :
    ReferenceColoring where
  color a b := if a = d.castSucc then incident (d.predAbove b)
    else if b = d.castSucc then incident (d.predAbove a)
    else c (d.predAbove a) (d.predAbove b)
  color_symm a b := by
    by_cases ha : a = d.castSucc <;> by_cases hb : b = d.castSucc <;>
      simp [ha, hb, c.color_symm]

theorem extend_survivors (c : Core.Coloring) (d : Omission)
    (incident : Vertex → FourColor) (a b : ReferenceVertex)
    (ha : a ≠ d.castSucc) (hb : b ≠ d.castSucc) :
    extend c d incident a b = c (d.predAbove a) (d.predAbove b) := by
  simp [extend, ha, hb]

@[simp] theorem extend_omitted (c : Core.Coloring) (d : Omission)
    (incident : Vertex → FourColor) (v : ReferenceVertex) :
    extend c d incident d.castSucc v = incident (d.predAbove v) := by
  simp [extend]

@[simp] theorem restrict_extend (c : Core.Coloring) (d : Omission)
    (incident : Vertex → FourColor) : restrictColoring (extend c d incident) d = c := by
  ext a b <;>
    simp [restrictColoring, extend, Fin.succAbove_ne, Fin.predAbove_succAbove]

theorem restrict_extend_good (c : Core.Coloring) (hc : NoMonochromaticTriangle c)
    (d : Omission) (incident : Vertex → FourColor) :
    NoMonochromaticTriangle (restrictColoring (extend c d incident) d) := by
  simpa only [restrict_extend] using hc

/-- A reference action only transports the actual sixty surviving vertices.
No triangle-free property of the completed reference is assumed. -/
theorem restriction_transformed_good (c : ReferenceColoring) (source target : Omission)
    (π : ReferenceVertex ≃ ReferenceVertex) (σ : Color ≃ Color)
    (hπ : π target.castSucc = source.castSucc)
    (hc : NoMonochromaticTriangle (restrictColoring c source)) :
    NoMonochromaticTriangle
      (restrictColoring (UniformK61.UnitTransport.transformed c π σ) target) := by
  let f := survivorEquiv source target π hπ
  have hf (v : Vertex) : source.castSucc.succAbove (f v) = π (target.castSucc.succAbove v) :=
    survivorMap_commutes source target π hπ v
  intro a b z hd hm
  apply hc (f a) (f b) (f z)
    ⟨f.injective.ne hd.1, f.injective.ne hd.2.1, f.injective.ne hd.2.2⟩
  have h1 := UniformK61.UnitTransport.colorEquiv.symm.injective
    (σ.injective (UniformK61.UnitTransport.colorEquiv.injective hm.1))
  have h2 := UniformK61.UnitTransport.colorEquiv.symm.injective
    (σ.injective (UniformK61.UnitTransport.colorEquiv.injective hm.2))
  constructor
  · change c (source.castSucc.succAbove (f a)) (source.castSucc.succAbove (f b)) =
      c (source.castSucc.succAbove (f a)) (source.castSucc.succAbove (f z))
    simpa only [hf] using h1
  · change c (source.castSucc.succAbove (f a)) (source.castSucc.succAbove (f z)) =
      c (source.castSucc.succAbove (f b)) (source.castSucc.succAbove (f z))
    simpa only [hf] using h2

#print axioms restrict_extend
#print axioms restriction_transformed_good
end UniformK60.ReferenceExtension
