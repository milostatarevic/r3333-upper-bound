import UniformK61.Core

set_option autoImplicit false
namespace UniformK61.Core

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The same finite base is used by every case in every profile. -/
theorem baseCNF_length : baseCNF.length = 156770 := by decide

theorem formula_length (units : List PhysicalUnit) :
    (formula units).length = 156770 + units.length := by
  simp only [formula,List.length_append,baseCNF_length,unitsCNF_length]

#print axioms baseCNF_length
#print axioms coloring_satisfies_formula
end UniformK61.Core
