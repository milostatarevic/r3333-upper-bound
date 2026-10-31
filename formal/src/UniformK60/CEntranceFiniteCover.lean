import UniformK60.CEntranceBridgeChecks
import UniformK60.CEntranceBridgeSoundness

set_option autoImplicit false
namespace UniformK60.CEntranceFiniteCover
open Ramsey61 UniformK60.Physical UniformK60.CEntranceSource
open UniformK60.CEntranceBridge CompletionC.NativeMatrices

/-- The finite bridge is complete for every actual canonical source word,
not merely for a supplied or assumed transport entry. -/
theorem source_satisfiable (mode : Mode) (p : Fin 737) (j : Fin (pairTable p).count)
    (h : Eligible mode p) (c : Host) (w : SourceWitness mode p j c) :
    ∃ k : CEntranceFormula.Case,∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (CEntranceFormula.formula k) := by
  obtain ⟨e,heMode,hePair,heRep,heValid⟩ := finite_bridge mode p j h
  subst mode
  subst p
  have hj : rep e=j := Fin.ext ((rep_value e heValid).trans heRep)
  have hw : SourceWitness e.mode e.pair (rep e) c := by rw [hj];exact w
  exact valid_satisfiable e heValid c hw

#print axioms source_satisfiable
end UniformK60.CEntranceFiniteCover
