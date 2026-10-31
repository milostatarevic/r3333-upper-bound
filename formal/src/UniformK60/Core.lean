import UniformK60.Physical

/-!
# One physical formula on K60

Every case uses the same one-hot edge variables and triangle exclusions. Its
only additional clauses are signed facts about physical edge colors. There
are no auxiliary variables or profile-dependent base constraints.
-/

set_option autoImplicit false

namespace UniformK60.Core
open Ramsey61 Ramsey61.DenseCounter

abbrev Vertex := UniformK60.Physical.Vertex
abbrev Color := UniformK60.Physical.Color
abbrev Coloring := UniformK60.Physical.Coloring
abbrev palette := UniformK60.Physical.palette
abbrev edgeVar := UniformK60.Physical.edgeVar
noncomputable abbrev physicalValuation := UniformK60.Physical.physicalValuation

/-- Lexicographic pairs, one-hot clauses, then lexicographic triples and colors. -/
def baseCNF : CNF :=
  UniformK60.Physical.physicalClauses ++ UniformK60.Physical.triangleClauses

/-- A positive or negative assertion about one edge of the physical K60. -/
structure PhysicalUnit where
  positive : Bool
  u : Vertex
  v : Vertex
  q : Color
  deriving Inhabited

def unitLiteral (u : PhysicalUnit) : Literal :=
  (u.positive, edgeVar u.u u.v u.q)

def unitsCNF (units : List PhysicalUnit) : CNF :=
  units.map fun u => [unitLiteral u]

def formula (units : List PhysicalUnit) : CNF := baseCNF ++ unitsCNF units

/-- Physical, global-color meaning of a unit, including exclusion of loops. -/
def UnitMatches (c : Coloring) (u : PhysicalUnit) : Prop :=
  u.u ≠ u.v ∧ if u.positive then c u.u u.v = palette u.q else c u.u u.v ≠ palette u.q

def UnitsMatch (c : Coloring) (units : List PhysicalUnit) : Prop :=
  ∀ u ∈ units, UnitMatches c u

theorem coloring_satisfies_base (c : Coloring) (hc : NoMonochromaticTriangle c) :
    FormulaSat (physicalValuation c) baseCNF := by
  exact (formulaSat_append _ _ _).mpr
    ⟨UniformK60.Physical.physicalValuation_physical c,
      UniformK60.Physical.physicalValuation_triangles c hc⟩

theorem positive_unit_iff (c : Coloring) (u v : Vertex) (q : Color) (hne : u ≠ v) :
    ClauseSat (physicalValuation c) [(true,edgeVar u v q)] ↔ c u v = palette q := by
  simp only [ClauseSat,List.mem_singleton,exists_eq_left]
  exact UniformK60.Physical.physicalValuation_edge c u v q hne

theorem negative_unit_iff (c : Coloring) (u v : Vertex) (q : Color) (hne : u ≠ v) :
    ClauseSat (physicalValuation c) [(false,edgeVar u v q)] ↔ c u v ≠ palette q := by
  simp only [ClauseSat,List.mem_singleton,exists_eq_left]
  rw [Bool.eq_false_iff]
  exact not_congr (UniformK60.Physical.physicalValuation_edge c u v q hne)

theorem unit_matches_satisfies (c : Coloring) (u : PhysicalUnit) (h : UnitMatches c u) :
    ClauseSat (physicalValuation c) [unitLiteral u] := by
  rcases u with ⟨positive,v,w,q⟩
  cases positive
  · exact (negative_unit_iff c v w q h.1).mpr h.2
  · exact (positive_unit_iff c v w q h.1).mpr h.2

theorem units_match_satisfies (c : Coloring) (units : List PhysicalUnit)
    (h : UnitsMatch c units) : FormulaSat (physicalValuation c) (unitsCNF units) := by
  intro clause hclause
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hclause
  exact unit_matches_satisfies c u (h u hu)

/-- Direct host-to-CNF implication. Every variable is an actual edge color. -/
theorem coloring_satisfies_formula (c : Coloring) (hc : NoMonochromaticTriangle c)
    (units : List PhysicalUnit) (h : UnitsMatch c units) :
    FormulaSat (physicalValuation c) (formula units) := by
  exact (formulaSat_append _ _ _).mpr
    ⟨coloring_satisfies_base c hc,units_match_satisfies c units h⟩

theorem unitLiteral_bounds (u : PhysicalUnit) (hne : u.u ≠ u.v) :
    1 ≤ (unitLiteral u).2 ∧ (unitLiteral u).2 < 7081 :=
  UniformK60.Physical.edgeVar_bounds u.u u.v u.q hne

@[simp] theorem unitsCNF_length (units : List PhysicalUnit) :
    (unitsCNF units).length = units.length := by simp [unitsCNF]

#print axioms coloring_satisfies_formula
end UniformK60.Core
