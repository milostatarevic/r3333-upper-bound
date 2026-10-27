import CompletionC.CommonCaseCard
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CompletionC.CommonCaseCount
open CompletionC.CommonCases

theorem executable_count:executableCount=55016:=by decide +kernel
/-- Exact cardinality of the admitted marked-case index set. -/
theorem native_case_count:Fintype.card Case=55016:=
 cardinality_eq_executable.trans executable_count
#print axioms native_case_count
end CompletionC.CommonCaseCount
