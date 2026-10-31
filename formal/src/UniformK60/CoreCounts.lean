import UniformK60.Core

set_option autoImplicit false
namespace UniformK60.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- All unordered pairs of distinct physical host vertices. -/
theorem orderedPairs_length : Physical.orderedPairs.length = 1770 := by decide

/-- Exactly one four-color value on each of the 1770 unordered edges. -/
theorem physicalClauses_length : Physical.physicalClauses.length = 12390 := by decide

/-- Four prohibitions for each of the 34220 unordered triples. -/
theorem triangleClauses_length : Physical.triangleClauses.length = 136880 := by decide

/-- The same finite K60 base is used by every marked case. -/
theorem baseCNF_length : baseCNF.length = 149270 := by
  simp only [baseCNF, List.length_append, physicalClauses_length, triangleClauses_length]

theorem formula_length (units : List PhysicalUnit) :
    (formula units).length = 149270 + units.length := by
  simp only [formula, List.length_append, baseCNF_length, unitsCNF_length]

#print axioms baseCNF_length
#print axioms coloring_satisfies_formula
end UniformK60.Core
