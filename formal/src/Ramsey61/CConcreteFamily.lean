import Ramsey61.CSeedData
import Ramsey61.CPhysicalNormalization

namespace Ramsey61.CConcreteFamily
open DenseCounter CEncodingCore CEncodingBase CPhysicalNormalization

/-- Exactly one physical edge-color literal; no auxiliary variable appears. -/
def unitLiteral (u : PhysicalUnit) : Literal := (u.positive,edgeVar u.u u.v u.q)
def seedLiterals (i : Fin 456) : List Literal := (seedData i).map unitLiteral
def seedCNF (i : Fin 456) : CNF := (seedLiterals i).map fun literal => [literal]

/-- The checked common base occurs once as a definition and is shared by456 suffixes. -/
def concreteFamily (i : Fin 456) : CNF := broaderBaseCNF ++ seedCNF i

/-- Physical meaning of each positive or negative archived seed unit. -/
def UnitMatches (c : Host) (u : PhysicalUnit) : Prop :=
  u.u ≠ u.v ∧ if u.positive then c u.u u.v = palette u.q else c u.u u.v ≠ palette u.q

def SeedMatches (c : Host) (i : Fin 456) : Prop := ∀ u ∈ seedData i, UnitMatches c u

theorem positive_unit_iff (c : Host) (u v : Vertex) (q : Color) (hne : u ≠ v) :
    ClauseSat (baseValuation c) [(true,edgeVar u v q)] ↔ c u v = palette q := by
  simp only [ClauseSat,List.mem_singleton,exists_eq_left]
  rw [baseValuation_physical c _ (edgeVar_bounds u v q hne).2]
  exact physicalValuation_edge c u v q hne

theorem negative_unit_iff (c : Host) (u v : Vertex) (q : Color) (hne : u ≠ v) :
    ClauseSat (baseValuation c) [(false,edgeVar u v q)] ↔ c u v ≠ palette q := by
  simp only [ClauseSat,List.mem_singleton,exists_eq_left]
  rw [baseValuation_physical c _ (edgeVar_bounds u v q hne).2,Bool.eq_false_iff]
  exact not_congr (physicalValuation_edge c u v q hne)

theorem unit_match_satisfies (c : Host) (u : PhysicalUnit) (h : UnitMatches c u) :
    ClauseSat (baseValuation c) [unitLiteral u] := by
  rcases u with ⟨positive,v,w,q⟩
  cases positive
  · exact (negative_unit_iff c v w q h.1).mpr h.2
  · exact (positive_unit_iff c v w q h.1).mpr h.2

theorem seedCNF_sat_iff (assignment : Valuation) (i : Fin 456) :
    FormulaSat assignment (seedCNF i) ↔ ∀ literal ∈ seedLiterals i, assignment literal.2 = literal.1 := by
  constructor
  · intro h literal hl
    have hc := h [literal] (List.mem_map.mpr ⟨literal,hl,rfl⟩)
    simpa only [ClauseSat,List.mem_singleton,exists_eq_left] using hc
  · intro h clause hc
    obtain ⟨literal,hl,rfl⟩ := List.mem_map.mp hc
    exact ⟨literal,by simp,h literal hl⟩

theorem concreteFamily_sat_iff (assignment : Valuation) (i : Fin 456) :
    FormulaSat assignment (concreteFamily i) ↔
      FormulaSat assignment broaderBaseCNF ∧
      ∀ literal ∈ seedLiterals i, assignment literal.2 = literal.1 := by
  rw [concreteFamily,formulaSat_append,seedCNF_sat_iff]

theorem seed_matches_satisfies (c : Host) (i : Fin 456) (h : SeedMatches c i) :
    FormulaSat (baseValuation c) (seedCNF i) := by
  intro clause hc
  obtain ⟨literal,hl,rfl⟩ := List.mem_map.mp hc
  obtain ⟨unit,hu,rfl⟩ := List.mem_map.mp hl
  exact unit_match_satisfies c unit (h unit hu)

theorem seed_matches_supplies_formula (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (hroot : RootConditions c) (i : Fin 456)
    (hmatch : SeedMatches c i) : FormulaSat (baseValuation c) (concreteFamily i) := by
  exact (formulaSat_append _ _ _).mpr
    ⟨coloring_satisfies_broaderBase c hc selectors hroot,seed_matches_satisfies c i hmatch⟩

/-- The remaining geometric cover, expressed only through actual physical
seed assertions after one simultaneous relabeling. This is NOT proved here.
No SAT or arbitrary auxiliary-valuation predicate occurs in this premise. -/
def NormalizedSeedCover : Prop := ∀ c : Host, NoMonochromaticTriangle c →
  SelectorX c → RootConditions c → 15 ≤ colorDegree c (palette 2) 33 →
  ∃ (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor) (i : Fin 456),
    RootConditions (relabel c e σ) ∧ SeedMatches (relabel c e σ) i

/-- The concrete replacement for the semantic part of physical_C_to_CNF_cover.
Only exhaustive normalized physical seed coverage remains as a premise. -/
theorem physical_C_to_concrete_family (coverage : NormalizedSeedCover) (c : Host)
    (hc : NoMonochromaticTriangle c) (selectors : SelectorX c) (witness : CExteriorWitness c) :
    ∃ i : Fin 456, ∃ assignment : Nat → Bool,
      ∀ clause ∈ concreteFamily i, ∃ literal ∈ clause, assignment literal.2 = literal.1 := by
  obtain ⟨e,σ,hgood,hsel,hroot,hmarked⟩ := exterior_witness_normalized c hc selectors witness
  obtain ⟨e',σ',i,hroot',hseed⟩ := coverage (relabel c e σ) hgood hsel hroot hmarked
  exact ⟨i,baseValuation (relabel (relabel c e σ) e' σ'),
    seed_matches_supplies_formula _ (relabel_noMono _ hgood e' σ')
      (relabel_selector _ hsel e' σ') hroot' i hseed⟩

#print axioms physical_C_to_concrete_family
#print axioms seed_matches_supplies_formula
end Ramsey61.CConcreteFamily
