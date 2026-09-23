import R4333Lean.CriticalTemplateDeletionData

/-!
# Certified vertex transitivity of the two critical K16 templates

For each chosen vertex, the generated map is checked to be a
colour-preserving permutation sending that vertex to label 15.  Consequently
deleting any vertex gives the fixed `Fin 15` restriction.
-/

namespace R4333

/-- Select one of the two critical K16 templates. -/
def k16Template (twisted : Bool) : EdgeColoring (Fin 16) ThreeColor :=
  if twisted then k16Twisted else k16Untwisted

/-- Its fixed deletion of vertex 15. -/
def k15Template (twisted : Bool) : EdgeColoring (Fin 15) ThreeColor :=
  if twisted then k15Twisted else k15Untwisted

/-- Explicit colour-preserving automorphism taking `deleted` to 15. -/
def k16TemplateToLastMap (twisted : Bool) (deleted : Fin 16) : Fin 16 → Fin 16 :=
  if twisted then k16TwistedToLastMaps.getD deleted id
  else k16UntwistedToLastMaps.getD deleted id

set_option maxRecDepth 100000 in
theorem k16TemplateToLastMap_bijective (twisted : Bool) (deleted : Fin 16) :
    Function.Bijective (k16TemplateToLastMap twisted deleted) := by
  cases twisted <;> fin_cases deleted <;> decide

noncomputable def k16TemplateToLastEquiv
    (twisted : Bool) (deleted : Fin 16) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (k16TemplateToLastMap twisted deleted)
    (k16TemplateToLastMap_bijective twisted deleted)

@[simp] theorem k16TemplateToLastEquiv_apply
    (twisted : Bool) (deleted x : Fin 16) :
    k16TemplateToLastEquiv twisted deleted x =
      k16TemplateToLastMap twisted deleted x := rfl

set_option maxRecDepth 100000 in
theorem k16TemplateToLastMap_deleted
    (twisted : Bool) (deleted : Fin 16) :
    k16TemplateToLastMap twisted deleted deleted = Fin.last 15 := by
  cases twisted <;> fin_cases deleted <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16TemplateToLastMap_preserves
    (twisted : Bool) (deleted : Fin 16) :
    ∀ u v, u ≠ v →
      k16Template twisted u v =
        k16Template twisted
          (k16TemplateToLastMap twisted deleted u)
          (k16TemplateToLastMap twisted deleted v) := by
  cases twisted <;> fin_cases deleted <;> decide

#print axioms R4333.k16TemplateToLastMap_bijective
#print axioms R4333.k16TemplateToLastMap_preserves

end R4333
