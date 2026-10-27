import UniformK61.CEntranceCatalogueDataComplete

set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter

abbrev Case := Fin 346

def caseUnits (k : Case) : List Core.PhysicalUnit :=
  Formula.units (Catalogue.five k) (Catalogue.leftType k) (Catalogue.rightType k)
    (Catalogue.pair k) (Catalogue.rep k)

def formula (k : Case) : CNF := Core.formula (caseUnits k)

/-- Exhaustive direct C entrance cover on all61 physical vertices. The
finite boundary has346 formulas, with no marked-cell critical template. -/
theorem actual_C_cover (c : Host) (hc : NoMonochromaticTriangle c)
    (witness : CExteriorWitness c) :
    ∃ k : Case, ∃ w : Valuation, FormulaSat w (formula k) := by
  obtain ⟨five,lt,rt,p,hp,j,w,hs⟩ := actual_C_cover_raw c hc witness
  obtain ⟨k,hpair,hrep,hfive,hleft,hright⟩ := Catalogue.complete five lt rt p hp j
  cases hpair
  have hj : Catalogue.rep k=j := Fin.ext hrep
  rw [←hj,←hfive,←hleft,←hright] at hs
  exact ⟨k,w,hs⟩

#print axioms actual_C_cover
end UniformK61.CEntrance
