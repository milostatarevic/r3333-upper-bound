import UniformK61.WholeProof

set_option autoImplicit false

example :
    (∀ k : UniformK61.WholeProof.Case,
      ¬∃ w : Ramsey61.DenseCounter.Valuation,
        Ramsey61.DenseCounter.FormulaSat w (UniformK61.WholeProof.formula k)) →
    ∀ c : Ramsey61.Host, ¬Ramsey61.NoMonochromaticTriangle c :=
  UniformK61.WholeProof.ramsey61

example : Fintype.card UniformK61.WholeProof.Case = 56723 :=
  UniformK61.WholeProof.native_case_count

#print axioms UniformK61.WholeProof.ramsey61
#print axioms UniformK61.WholeProof.native_case_count
