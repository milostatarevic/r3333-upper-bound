import PricingIntegration.SparseCounter

namespace PricingIntegration.MultiSparseCounter
open Finset Ramsey61.DenseCounter PricingIntegration.FoldedThreshold
open PricingIntegration.SparseCounter

/-- Prefix allocation of complete sparse-counter intervals. Empty counters
may share a boundary but never own an auxiliary atom. -/
def start {N : Nat} (base : Nat) (size : Fin N → Nat) (i : Fin N) : Nat :=
  base + ∑ j ∈ Iio i, size j

theorem base_le_start {N : Nat} (base : Nat) (size : Fin N → Nat) (i : Fin N) :
    base ≤ start base size i := Nat.le_add_right _ _

theorem end_le_next {N : Nat} (base : Nat) (size : Fin N → Nat)
    {i j : Fin N} (hij : i < j) : start base size i + size i ≤ start base size j := by
  have hs : insert i (Iio i) ⊆ Iio j := by
    intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact mem_Iio.mpr hij
    · exact mem_Iio.mpr (lt_trans (mem_Iio.mp hk) hij)
  have hh := sum_le_sum_of_subset_of_nonneg (f := size) hs (fun a _ _ => Nat.zero_le (size a))
  rw [sum_insert (by simp)] at hh
  unfold start
  omega

def size {N : Nat} (xs : Fin N → List Lit) (height : Fin N → Nat) (i : Fin N) : Nat :=
  offset (height i) (xs i).length

abbrev AllocatedCell {N : Nat} (xs : Fin N → List Lit) (height : Fin N → Nat) :=
  (i : Fin N) × Cell (xs i).length (height i)

def allocatedAtom {N : Nat} (base : Nat) (xs : Fin N → List Lit) (height : Fin N → Nat)
    (p : AllocatedCell xs height) : Nat :=
  cellAtom (start base (size xs height) p.1) p.2

theorem cellAtom_bounds (s rows h : Nat) (p : Cell rows h) :
    s ≤ cellAtom s p ∧ cellAtom s p < s + offset h rows := by
  have ho := offset_mono h (show p.1.1.val + 1 ≤ rows by omega)
  rw [offset_succ] at ho
  have hc : p.1.2.val < min (p.1.1.val + 1) h := by omega
  unfold cellAtom atom
  omega

theorem allocatedAtom_injective {N : Nat} (base : Nat)
    (xs : Fin N → List Lit) (height : Fin N → Nat) :
    Function.Injective (allocatedAtom base xs height) := by
  intro p q he
  have hp := cellAtom_bounds (start base (size xs height) p.1) _ _ p.2
  have hq := cellAtom_bounds (start base (size xs height) q.1) _ _ q.2
  have hi : p.1 = q.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbound := end_le_next base (size xs height) hlt
      change start base (size xs height) p.1 + offset (height p.1) (xs p.1).length ≤ _ at hbound
      change cellAtom (start base (size xs height) p.1) p.2 =
        cellAtom (start base (size xs height) q.1) q.2 at he
      omega
    · have hbound := end_le_next base (size xs height) hgt
      change start base (size xs height) q.1 + offset (height q.1) (xs q.1).length ≤ _ at hbound
      change cellAtom (start base (size xs height) p.1) p.2 =
        cellAtom (start base (size xs height) q.1) q.2 at he
      omega
  cases p with
  | mk i p =>
    cases q with
    | mk j q =>
      dsimp at hi
      subst j
      have hpq := cellAtom_injective (start base (size xs height) i) (xs i).length (height i) he
      cases hpq
      rfl

noncomputable def extend {N : Nat} (v : Valuation) (base : Nat)
    (xs : Fin N → List Lit) (height : Fin N → Nat) : Valuation := fun a =>
  if h : ∃ p : AllocatedCell xs height, allocatedAtom base xs height p = a then
    let p := Classical.choose h
    decide (p.2.1.2.val + 1 ≤ prefixCountSigned v (xs p.1) (p.2.1.1.val + 1))
  else v a

theorem extend_at_cell {N : Nat} (v : Valuation) (base : Nat)
    (xs : Fin N → List Lit) (height : Fin N → Nat) (p : AllocatedCell xs height) :
    extend v base xs height (allocatedAtom base xs height p) =
      decide (p.2.1.2.val + 1 ≤ prefixCountSigned v (xs p.1) (p.2.1.1.val + 1)) := by
  have he : ∃ q : AllocatedCell xs height, allocatedAtom base xs height q = allocatedAtom base xs height p := ⟨p,rfl⟩
  rw [extend,dif_pos he]
  have hp : Classical.choose he = p := allocatedAtom_injective base xs height (Classical.choose_spec he)
  exact congrArg (fun z : AllocatedCell xs height =>
    decide (z.2.1.2.val + 1 ≤ prefixCountSigned v (xs z.1) (z.2.1.1.val + 1))) hp

theorem extend_before_base {N : Nat} (v : Valuation) (base : Nat)
    (xs : Fin N → List Lit) (height : Fin N → Nat) (a : Nat) (ha : a < base) :
    extend v base xs height a = v a := by
  have hn : ¬∃ p : AllocatedCell xs height, allocatedAtom base xs height p = a := by
    rintro ⟨p,hp⟩
    have hb := (cellAtom_bounds (start base (size xs height) p.1) _ _ p.2).1
    have hs := base_le_start base (size xs height) p.1
    change cellAtom (start base (size xs height) p.1) p.2 = a at hp
    omega
  rw [extend,dif_neg hn]

theorem holds_threshold {N : Nat} (v : Valuation) (base : Nat)
    (xs : Fin N → List Lit) (height : Fin N → Nat) (i : Fin N) (r k : Nat)
    (hr : r ≤ (xs i).length) (hk : k ≤ height i) :
    Holds (extend v base xs height) (threshold (start base (size xs height) i) (height i) r k) ↔
      k ≤ prefixCountSigned v (xs i) r := by
  have hb : prefixCountSigned v (xs i) r ≤ r :=
    le_trans List.countP_le_length (List.length_take_le _ _)
  by_cases hz : k = 0
  · simp [threshold,hz,Holds]
  by_cases hkr : r < k
  · simp [threshold,hz,hkr,Holds]
    omega
  let p : AllocatedCell xs height :=
    ⟨i,⟨(⟨r-1,by omega⟩,⟨k-1,by omega⟩),by change k-1 ≤ r-1; omega⟩⟩
  rw [threshold,if_neg hz,if_neg hkr]
  change extend v base xs height (allocatedAtom base xs height p) = true ↔ _
  rw [extend_at_cell]
  have hr' : r - 1 + 1 = r := by omega
  have hk' : k - 1 + 1 = k := by omega
  simp only [p,hr',hk',decide_eq_true_eq]

theorem cell_satisfied {N : Nat} (v : Valuation) (base : Nat)
    (xs : Fin N → List Lit) (height : Fin N → Nat)
    (hinputs : ∀ i, ∀ l ∈ xs i, l.2 < base)
    (i : Fin N) (r k : Nat) (hr : r < (xs i).length) (hk : k < min (r + 1) (height i)) :
    SignalFormulaSat (extend v base xs height)
      (cell (xs i) (start base (size xs height) i) (height i) r k) := by
  rw [cell,recurrenceClauses_sat_iff]
  rw [holds_threshold v base xs height i _ _ (by omega) (by omega),
    holds_threshold v base xs height i _ _ (by omega) (by omega),
    holds_threshold v base xs height i _ _ (by omega) (by omega)]
  simp only [Holds,List.getElem?_eq_getElem hr,Option.getD_some]
  rw [extend_before_base v base xs height _ (hinputs i _ (List.getElem_mem hr)),
    prefixCountSigned_succ v (xs i) r hr]
  by_cases heq : v (xs i)[r].2 = (xs i)[r].1
  · simp [value,heq]
    omega
  · simp [value,heq]

/-- All independent sparse counters have one constructed valuation. Primary
atoms are preserved; every normalized clause and every threshold meaning
is established simultaneously across disjoint auxiliary intervals. -/
theorem simultaneous_satisfying_extension {N : Nat}
    (v : Valuation) (base : Nat) (xs : Fin N → List Lit) (height : Fin N → Nat)
    (hinputs : ∀ i, ∀ l ∈ xs i, l.2 < base) :
    ∃ w : Valuation, (∀ a < base, w a = v a) ∧
      (∀ i, FormulaSat w (normalizeFormula (signals (xs i) (start base (size xs height) i) (height i)))) ∧
      (∀ i, ∀ r ≤ (xs i).length, ∀ k ≤ height i,
        Holds w (threshold (start base (size xs height) i) (height i) r k) ↔
          k ≤ prefixCountSigned v (xs i) r) := by
  refine ⟨extend v base xs height,fun a ha => extend_before_base v base xs height a ha,?_,?_⟩
  · intro i
    apply normalizeFormula_sound
    intro cl hcl
    simp only [signals,List.mem_flatMap] at hcl
    obtain ⟨row,hr,col,hc,hm⟩ := hcl
    exact cell_satisfied v base xs height hinputs i row col
      (List.mem_range.mp hr) (List.mem_range.mp hc) cl hm
  · exact fun i r hr k hk => holds_threshold v base xs height i r k hr hk

#print axioms allocatedAtom_injective
#print axioms simultaneous_satisfying_extension
end PricingIntegration.MultiSparseCounter
