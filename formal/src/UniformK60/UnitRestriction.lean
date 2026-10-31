import UniformK60.UnitTransport
import Mathlib.Data.Fin.Embedding

/-!
Restriction of signed reference facts to the actual K60. A reference
coloring need not be good: only its restriction to the sixty surviving
positions is required to have no monochromatic triangle. In particular,
this module never transfers a K61 UNSAT result to a smaller graph.
-/

set_option autoImplicit false
namespace UniformK60.UnitRestriction
open Ramsey61 UniformK60.Physical

abbrev ReferenceVertex := Fin 61
abbrev ReferenceColoring := EdgeColoring ReferenceVertex FourColor

/-- The common61-position reference format used by the finite source lists. -/
structure ReferenceUnit where
  positive : Bool
  u : ReferenceVertex
  v : ReferenceVertex
  q : Color
  deriving Inhabited

/-- All selected omitted positions precede the distinguished last mark. -/
abbrev Omission := Fin 60

def survives (d : Omission) (u : ReferenceUnit) : Prop :=
  u.u ≠ d.castSucc ∧ u.v ≠ d.castSucc

instance (d : Omission) (u : ReferenceUnit) : Decidable (survives d u) := by
  unfold survives
  infer_instance

def referenceMatches (c : ReferenceColoring) (u : ReferenceUnit) : Prop :=
  u.u ≠ u.v ∧
    if u.positive then c u.u u.v = palette u.q else c u.u u.v ≠ palette u.q

def restrictColoring (c : ReferenceColoring) (d : Omission) : Core.Coloring where
  color a b := c (d.castSucc.succAbove a) (d.castSucc.succAbove b)
  color_symm _ _ := c.color_symm _ _

def restrictedFact (d : Omission) (u : ReferenceUnit) : Core.PhysicalUnit :=
  ⟨u.positive, d.predAbove u.u, d.predAbove u.v, u.q⟩

def restrictUnits (d : Omission) (units : List ReferenceUnit) : List Core.PhysicalUnit :=
  (units.filter (fun u => decide (survives d u))).map (restrictedFact d)

theorem restricted_fact_matches (c : ReferenceColoring) (d : Omission)
    (u : ReferenceUnit) (hu : survives d u) (hm : referenceMatches c u) :
    Core.UnitMatches (restrictColoring c d) (restrictedFact d u) := by
  refine ⟨?_, ?_⟩
  · intro he
    change d.predAbove u.u = d.predAbove u.v at he
    apply hm.1
    have hh := congrArg d.castSucc.succAbove he
    simpa only [Fin.succAbove_predAbove hu.1, Fin.succAbove_predAbove hu.2] using hh
  · change (if u.positive then
      c (d.castSucc.succAbove (d.predAbove u.u))
        (d.castSucc.succAbove (d.predAbove u.v)) = palette u.q
      else c (d.castSucc.succAbove (d.predAbove u.u))
        (d.castSucc.succAbove (d.predAbove u.v)) ≠ palette u.q)
    simpa only [Fin.succAbove_predAbove hu.1, Fin.succAbove_predAbove hu.2] using hm.2

/-- Only facts away from the omitted reference position are premises. -/
theorem restrict_units_match (c : ReferenceColoring) (d : Omission)
    (units : List ReferenceUnit)
    (hm : ∀ u ∈ units, survives d u → referenceMatches c u) :
    Core.UnitsMatch (restrictColoring c d) (restrictUnits d units) := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  have hfilter := List.mem_filter.mp hv
  have hs : survives d v := of_decide_eq_true hfilter.2
  exact restricted_fact_matches c d v hs (hm v hfilter.1 hs)

/-- Signed integer ordering is the serialization used by the frozen E
inputs and by the K60 A/B/D catalogue. Multiplicity is preserved. -/
def signedLiteral (u : Core.PhysicalUnit) : Int :=
  if u.positive then (Core.edgeVar u.u u.v u.q : Int)
  else -(Core.edgeVar u.u u.v u.q : Int)

def sortUnits (units : List Core.PhysicalUnit) : List Core.PhysicalUnit :=
  units.mergeSort (fun a b => decide (signedLiteral a ≤ signedLiteral b))

theorem sort_units_match (c : Core.Coloring) (units : List Core.PhysicalUnit)
    (hm : Core.UnitsMatch c units) : Core.UnitsMatch c (sortUnits units) := by
  intro u hu
  exact hm u (List.mem_mergeSort.mp hu)

def sortedRestriction (d : Omission) (units : List ReferenceUnit) :
    List Core.PhysicalUnit := sortUnits (restrictUnits d units)

def formula (d : Omission) (units : List ReferenceUnit) : DenseCounter.CNF :=
  Core.formula (sortedRestriction d units)

/-- Fresh K60 goodness plus true restricted facts gives a satisfying
assignment to the exact restricted formula. No good reference host is used. -/
theorem restriction_satisfiable (c : ReferenceColoring) (d : Omission)
    (units : List ReferenceUnit)
    (hc : NoMonochromaticTriangle (restrictColoring c d))
    (hm : ∀ u ∈ units, survives d u → referenceMatches c u) :
    ∃ w : DenseCounter.Valuation, DenseCounter.FormulaSat w (formula d units) := by
  refine ⟨Core.physicalValuation (restrictColoring c d), ?_⟩
  exact Core.coloring_satisfies_formula _ hc _
    (sort_units_match _ _ (restrict_units_match c d units hm))

/-- The bijection on survivors induced by a reference permutation that
maps the target omission to the source omission. -/
def survivorMap (source target : Omission) (π : ReferenceVertex ≃ ReferenceVertex)
    (v : Vertex) : Vertex := source.predAbove (π (target.castSucc.succAbove v))

theorem survivorMap_commutes (source target : Omission)
    (π : ReferenceVertex ≃ ReferenceVertex) (hπ : π target.castSucc = source.castSucc)
    (v : Vertex) :
    source.castSucc.succAbove (survivorMap source target π v) =
      π (target.castSucc.succAbove v) := by
  apply Fin.succAbove_predAbove
  intro he
  have hh := π.injective (he.trans hπ.symm)
  exact Fin.succAbove_ne _ _ hh

theorem survivorMap_injective (source target : Omission)
    (π : ReferenceVertex ≃ ReferenceVertex) (hπ : π target.castSucc = source.castSucc) :
    Function.Injective (survivorMap source target π) := by
  intro u v he
  have hh := congrArg source.castSucc.succAbove he
  rw [survivorMap_commutes source target π hπ u,
    survivorMap_commutes source target π hπ v] at hh
  exact Fin.succAbove_right_injective (π.injective hh)

noncomputable def survivorEquiv (source target : Omission)
    (π : ReferenceVertex ≃ ReferenceVertex) (hπ : π target.castSucc = source.castSucc) :
    Vertex ≃ Vertex :=
  Equiv.ofBijective (survivorMap source target π)
    ⟨survivorMap_injective source target π hπ,
      Finite.surjective_of_injective (survivorMap_injective source target π hπ)⟩

/-- Exact numerical deletion convention: decrement precisely positions
strictly above the omitted position. -/
theorem restricted_position_value (d : Omission) (v : ReferenceVertex) :
    (d.predAbove v).val = v.val - if d.val < v.val then 1 else 0 := by
  by_cases h : d.castSucc < v
  · rw [Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_pred]
    have hval : d.val < v.val := h
    simp [hval]
  · have hle : v ≤ d.castSucc := le_of_not_gt h
    rw [Fin.predAbove_of_le_castSucc _ _ hle]
    simp only [Fin.coe_castPred]
    have hval : ¬d.val < v.val := h
    simp [hval]

#print axioms restriction_satisfiable
#print axioms survivorMap_commutes
#print axioms survivorMap_injective
end UniformK60.UnitRestriction
