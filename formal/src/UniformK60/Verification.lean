import UniformK60.FiniteBoundary
import UniformK60.CoreCounts
import UniformK61.CommonUnitCache

/-! Verification root for the complete mathematical reduction to the explicit
finite K60 CNF catalogue. Native UNSAT evidence remains an external premise. -/

#check @UniformK60.ramsey60_of_exact_unsat
#print axioms UniformK60.ramsey60_of_exact_unsat
#check @UniformK60.CEntranceComplete.no_entrance_of_all_unsat
#print axioms UniformK60.CEntranceComplete.no_entrance_of_all_unsat

example (h : UniformK60.ExactInputs.AllUnsat) :
    ∀ c : Ramsey61.EdgeColoring (Fin 60) (Bool × Bool),
      ¬Ramsey61.NoMonochromaticTriangle c :=
  UniformK60.ramsey60_of_exact_unsat h

#print axioms UniformK60.ramsey60_of_reduction_obligations
#print axioms UniformK60.Core.coloring_satisfies_formula
#print axioms UniformK60.Core.baseCNF_length
