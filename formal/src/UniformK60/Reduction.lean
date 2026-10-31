import UniformK60.BalancedStructure

/-!
An intermediate mathematical reduction, not the final SAT-bound theorem.
The remaining hypotheses must be discharged by exact formula covers and
their computational exclusions before claiming the K60 bound.
-/

set_option autoImplicit false
namespace UniformK60
open Ramsey61 Finset

def CommonCriticalPair (c : Host) : Prop :=
  ∃ high : Finset FourColor, high.card = 2 ∧
    ∀ v : Fin 60, criticalColors c v = high

/-- The upper degree vector associated with the common pair, before
renaming its colors to 0 and 1. -/
def pairCap (high : Finset FourColor) (q : FourColor) : Nat :=
  if q ∈ high then 16 else 14

theorem common_pair_degree_caps (c : Host) (hc : NoMonochromaticTriangle c)
    (hpair : CommonCriticalPair c) :
    ∃ high : Finset FourColor, high.card = 2 ∧
      ∀ v : Fin 60, ∀ q : FourColor, colorDegree c q v ≤ pairCap high q := by
  obtain ⟨high, hcard, hhigh⟩ := hpair
  refine ⟨high, hcard, ?_⟩
  intro v q
  by_cases hq : q ∈ high
  · simpa only [pairCap, if_pos hq] using fourColor_colorDegree_le_sixteen c hc q v
  · have hnot : ¬15 ≤ colorDegree c q v := by
      intro h
      have hm := (mem_criticalColors c v q).mpr h
      rw [hhigh v] at hm
      exact hq hm
    simp only [pairCap, if_neg hq]
    omega

/-- In named common-pair coordinates, the upper bounds and the degree sum
give exactly the four vectors (16,16,14,14) minus one unit vector. -/
theorem named_degree_vectors (a b d e : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hd : d ≤ 14) (he : e ≤ 14)
    (hsum : a + b + d + e = 59) :
    (a = 15 ∧ b = 16 ∧ d = 14 ∧ e = 14) ∨
    (a = 16 ∧ b = 15 ∧ d = 14 ∧ e = 14) ∨
    (a = 16 ∧ b = 16 ∧ d = 13 ∧ e = 14) ∨
    (a = 16 ∧ b = 16 ∧ d = 14 ∧ e = 13) := by
  omega

theorem tickets_and_no_entrance_force_common_pair
    (c : Host) (hc : NoMonochromaticTriangle c)
    (bounds : StrictTicketBounds c) (none : ¬ CExteriorWitness c) :
    CommonCriticalPair c :=
  BalancedStructure.synchronized_common_pair c hc
    (no_C_witness_forces_synchronized c hc bounds none)

/-- Composition of the three remaining semantic proof obligations.
This intentionally does not call them an established native UNSAT boundary:
the K60 formula covers and exact input bindings still have to be proved. -/
theorem ramsey60_of_reduction_obligations
    (hTickets : ∀ c : Host, NoMonochromaticTriangle c → StrictTicketBounds c)
    (hEntrance : ∀ c : Host, NoMonochromaticTriangle c → ¬ CExteriorWitness c)
    (hBalanced : ∀ c : Host, NoMonochromaticTriangle c → CommonCriticalPair c → False) :
    ∀ c : Host, ¬ NoMonochromaticTriangle c := by
  intro c hc
  exact hBalanced c hc
    (tickets_and_no_entrance_force_common_pair c hc (hTickets c hc) (hEntrance c hc))

#print axioms tickets_and_no_entrance_force_common_pair
#print axioms common_pair_degree_caps
#print axioms named_degree_vectors
#print axioms ramsey60_of_reduction_obligations
end UniformK60
