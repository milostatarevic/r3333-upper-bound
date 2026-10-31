import UniformK60.BalancedEncodingValuation

/-! Exact support-selection clauses with fresh selectors. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK61.BalancedEncoding (sat_map sat_flatMap oneHot_sat)

structure GuardGeometry (n p : Nat) where
  center : Vertex
  member : Fin n → Vertex
  color : Color
  pattern : Fin p → Finset (Fin n)
  selector : Fin p → Nat
  distinct : ∀ m, center ≠ member m

def guardAtom {n p : Nat} (g : GuardGeometry n p) (m : Fin n) : Nat :=
  edgeVar g.center (g.member m) g.color

def guardClauses {n p : Nat} (g : GuardGeometry n p) : CNF :=
  oneHot g.selector ++ (List.finRange p).flatMap fun i =>
    (List.finRange n).map fun m =>
      [negative (g.selector i),(decide (m ∈ g.pattern i),guardAtom g m)]

structure GuardWitness {n p : Nat} (c : Host) (g : GuardGeometry n p) where
  chosen : Fin p
  membership : ∀ m, (c g.center (g.member m) = palette g.color) ↔ m ∈ g.pattern chosen

theorem guard_sat {n p : Nat} {c : Host} {g : GuardGeometry n p}
    (v : Valuation) (hp : PhysicalMatches v c) (w : GuardWitness c g)
    (hs : ∀ i, v (g.selector i) = decide (i = w.chosen)) :
    FormulaSat v (guardClauses g) := by
  rw [guardClauses,formulaSat_append]
  refine ⟨oneHot_sat v g.selector w.chosen hs,?_⟩
  apply sat_flatMap
  intro i _
  apply sat_map
  intro m _
  by_cases hi : i = w.chosen
  · subst i
    refine ⟨(decide (m ∈ g.pattern w.chosen),guardAtom g m),by simp,?_⟩
    change v (edgeVar g.center (g.member m) g.color) = _
    simp only [hp _ _ (g.distinct m),w.membership m]
  · exact ⟨negative (g.selector i),by simp,by simp [negative,hs,hi]⟩

noncomputable def extendGuard {n p : Nat} {c : Host} {g : GuardGeometry n p}
    (old : Valuation) (w : GuardWitness c g) (a : Nat) : Bool := by
  classical
  exact if h : ∃ i, g.selector i = a then decide (Classical.choose h = w.chosen) else old a

theorem extendGuard_at {n p : Nat} {c : Host} {g : GuardGeometry n p}
    (old : Valuation) (w : GuardWitness c g) (hi : Function.Injective g.selector) (i : Fin p) :
    extendGuard old w (g.selector i) = decide (i = w.chosen) := by
  classical
  have he : ∃ j, g.selector j = g.selector i := ⟨i,rfl⟩
  simp only [extendGuard,dif_pos he]
  rw [hi (Classical.choose_spec he)]

theorem extendGuard_below {n p : Nat} {c : Host} {g : GuardGeometry n p}
    (old : Valuation) (w : GuardWitness c g) (top : Nat)
    (fresh : ∀ i, top < g.selector i) (a : Nat) (ha : a ≤ top) :
    extendGuard old w a = old a := by
  classical
  have he : ¬∃ i, g.selector i = a := by
    rintro ⟨i,hi⟩
    have h := fresh i
    omega
  simp only [extendGuard,dif_neg he]

theorem guard_extension {n p : Nat} {c : Host} {g : GuardGeometry n p}
    (old : Valuation) (hp : PhysicalMatches old c) (w : GuardWitness c g)
    (top : Nat) (htop : 7080 ≤ top) (hi : Function.Injective g.selector)
    (fresh : ∀ i, top < g.selector i) :
    ∃ v : Valuation, FormulaSat v (guardClauses g) ∧
      (∀ a, a ≤ top → v a = old a) ∧ PhysicalMatches v c := by
  let v := extendGuard old w
  have unchanged : ∀ a, a ≤ top → v a = old a := extendGuard_below old w top fresh
  have phys : PhysicalMatches v c := by
    intro a b hab q
    have bound := (edgeVar_bounds a b q hab).2
    exact (unchanged _ (by omega)).trans (hp a b hab q)
  exact ⟨v,guard_sat v phys w (extendGuard_at old w hi),unchanged,phys⟩

#print axioms guard_extension
end UniformK60.BalancedEncoding
