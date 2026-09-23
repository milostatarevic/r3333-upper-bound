import PricingC.AnchorTables

namespace PricingC.FourAnchorTables
open PricingC PricingC.AnchorTables PricingG.Completion72

def pathColor (a b : Fin 4) : Fin 3 := if a.val + 1 = b.val ∨ b.val + 1 = a.val then 1 else 2

def planeRoles : Fin 4 → Fin 16 := ![0,3,5,6]
def starRoles (i : Fin 4) : Fin 16 := generators ⟨i.val,by omega⟩

def PathOn (row : Fin 72) (roles : Fin 4 → Fin 16) : Prop :=
  ∀ a b : Fin 4, a ≠ b → referenceColor row (roles a) (roles b) = pathColor a b

instance (row : Fin 72) (roles : Fin 4 → Fin 16) : Decidable (PathOn row roles) :=
  inferInstanceAs (Decidable (∀ a b : Fin 4, a ≠ b → _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem star_path_completes_cycle (row : Fin 72) : PathOn row starRoles ↔ HasCycleAnchor row := by
  fin_cases row <;> decide

def nonstarIndex : Fin 2 → Fin 72 := ![39,46]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nonstar_exhaustive (row : Fin 72) : PathOn row planeRoles ↔ ∃ i : Fin 2, nonstarIndex i = row := by
  fin_cases row <;> decide

#print axioms star_path_completes_cycle
#print axioms nonstar_exhaustive
end PricingC.FourAnchorTables
