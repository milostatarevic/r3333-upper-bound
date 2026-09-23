import Ramsey61.GuardedEntrance

namespace Ramsey61

/-- Positive/negative propositional literal; variable names are natural numbers. -/
abbrev Literal := Bool × Nat
abbrev CNF := List (List Literal)

def Satisfiable (f : CNF) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ f, ∃ literal ∈ clause, assignment literal.2 = literal.1

/-- A family indexed by the 456 C cases. The concrete instance is
`Ramsey61.CConcreteFamily.concreteFamily`, consumed by
`PricingIntegration.NativeWholeProof.ramsey61`. -/
abbrev CFormulaFamily := Fin 456 → CNF

/-- Interfaces used by the parametric composition lemma.
`PricingIntegration.NativeWholeProof.ramsey61` supplies all three fields
with proved terms for the concrete formula family. None is an added axiom. -/
structure RemainingBaselineBridges (family : CFormulaFamily) : Prop where
  /-- All A/B/D extraction, classification, exhaustive covers and refutations. -/
  abd_supplied_root_selector : ∀ c : Host, NoMonochromaticTriangle c → SelectorX c
  /-- Exact guarded G exclusion, including its structural argument and the
  two retained finite covers. Uniform host to G is proved in GuardedEntrance. -/
  guarded_G_exclusion : ∀ c : Host, NoMonochromaticTriangle c →
    ∀ (r : Fin 61) (p q : FourColor), RegularOverlapGuard c r p q → False
  /-- Physical C coverage and a satisfying auxiliary assignment for this family.
  The final endpoint supplies `PricingIntegration.CComplete.physical_C_to_exact_family`. -/
  physical_C_to_CNF_cover : ∀ c : Host, NoMonochromaticTriangle c →
    SelectorX c → CExteriorWitness c → ∃ i : Fin 456, Satisfiable (family i)

/-- The incidence entrance parameterized by its graph and guarded-G implications.
The composition below supplies them from the proved structural argument and
the supplied guard exclusion. -/
theorem root_entrance_conditional (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c)
    (synchronized_to_uniform : SynchronizedCE c → UniformCommonHighPair c)
    (uniform_G_exclusion : UniformCommonHighPair c → False) : CExteriorWitness c := by
  classical
  by_contra none
  have sync := no_C_witness_forces_synchronized_CE c hc selectors none
  exact uniform_G_exclusion (synchronized_to_uniform sync)

/-- Parametric composition of the root entrance, case cover and refutations.
The complete endpoint `PricingIntegration.NativeWholeProof.ramsey61` instantiates
the concrete family and all three mathematical interfaces; only its explicit
`AllNativeUnsat` computational premise remains. -/
theorem ramsey61_conditional (family : CFormulaFamily)
    (bridges : RemainingBaselineBridges family)
    (all456_unsat : ∀ i : Fin 456, ¬ Satisfiable (family i)) :
    ∀ c : Host, ¬ NoMonochromaticTriangle c := by
  intro c hc
  have selectors := bridges.abd_supplied_root_selector c hc
  have witness := root_entrance_conditional c hc selectors
    (synchronized_uniform_complete c hc)
    (fun uniform => by
      obtain ⟨p, q, guard⟩ := uniform_host_has_regular_overlap c hc uniform 0
      exact bridges.guarded_G_exclusion c hc 0 p q guard)
  obtain ⟨i, hi⟩ := bridges.physical_C_to_CNF_cover c hc selectors witness
  exact all456_unsat i hi

end Ramsey61
