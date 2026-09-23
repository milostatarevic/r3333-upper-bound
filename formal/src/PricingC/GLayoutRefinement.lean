import PricingC.GCaseCore

namespace PricingC.GLayoutRefinement
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.LocalRelations
open PricingIntegration.CoreLayout PricingC.GIsomorphic PricingG.Completion72

def Refines (fine coarse : CoreBase) : Prop :=
  ∀ u v q, Allows (fine u v) q → Allows (coarse u v) q

theorem high_unit_of_refines (fine coarse : CoreBase) (h : Refines fine coarse)
    (u v : Fin 33) (q : Color) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hc : coarse u v = some q) : fine u v = some q := by
  cases hf : fine u v with
  | none =>
    have hh := h u v 2 (by simp only [hf,Allows]; exact Or.inl trivial)
    have he : (2 : Color) = q := by simpa only [hc,Allows] using hh
    exact False.elim (hq2 he.symm)
  | some r =>
    have hh := h u v r (by simp only [hf,Allows])
    have he : r = q := by simpa only [hc,Allows] using hh
    exact congrArg some he

theorem layoutValid_of_refines (fine coarse : CoreBase) (h : Refines fine coarse)
    (l : ScopeLayout) (hl : LayoutValid coarse l) : LayoutValid fine l := by
  refine ⟨hl.1,?_,?_,hl.2.2.2.1,hl.2.2.2.2.1,?_⟩
  · intro k
    refine ⟨(hl.2.1 k).1,high_unit_of_refines fine coarse h l.owner (l.slots k) (omittedColor l.side) ?_ ?_ (hl.2.1 k).2⟩
    all_goals cases l.side <;> decide
  · intro j k hjk q hq
    exact hl.2.2.1 j k hjk q (h _ _ _ hq)
  · intro k hk j q hq
    exact hl.2.2.2.2.2 k hk j q (h _ _ _ hq)

def eraseLow : Option Color → Option Color
  | none => none
  | some q => if q=2 ∨ q=3 then none else some q

def eraseCore (b : CoreBase) : CoreBase := fun u v => eraseLow (b u v)

theorem erase_refines (b : CoreBase) : Refines b (eraseCore b) := by
  intro u v q hq
  change Allows (eraseLow (b u v)) q
  cases h : b u v with
  | none => simpa only [h,eraseLow] using hq
  | some r =>
    have hr : q=r := by simpa only [h,Allows] using hq
    subst q
    fin_cases r <;> simp [eraseLow,Allows]

theorem erase_xPalette_reference (i j : Fin 72) (a b : Fin 16) :
    eraseLow (some (xPalette (referenceColor i a b))) =
      eraseLow (some (xPalette (referenceColor j a b))) := by
  simp only [referenceColor]
  split_ifs <;> rfl

theorem erase_yPalette_reference (i j : Fin 72) (a b : Fin 16) :
    eraseLow (some (yPalette (referenceColor i a b))) =
      eraseLow (some (yPalette (referenceColor j a b))) := by
  simp only [referenceColor]
  split_ifs <;> rfl

def skeleton (g : Fin 25) : CoreBase := eraseCore (baseCore 0 0 g)

theorem baseCore_erase_eq (x : Fin 2) (y : Fin 72) (g : Fin 25) :
    eraseCore (baseCore x y g) = skeleton g := by
  funext a b
  simp only [eraseCore,skeleton,baseCore]
  split_ifs <;> first
    | rfl
    | exact erase_xPalette_reference _ _ _ _
    | exact erase_yPalette_reference _ _ _ _

theorem baseCore_refines_skeleton (x : Fin 2) (y : Fin 72) (g : Fin 25) :
    Refines (baseCore x y g) (skeleton g) := by
  rw [← baseCore_erase_eq x y g]
  exact erase_refines _

#print axioms layoutValid_of_refines
#print axioms baseCore_refines_skeleton
end PricingC.GLayoutRefinement
