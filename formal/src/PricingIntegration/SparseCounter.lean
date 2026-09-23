import PricingIntegration.FoldedThreshold

namespace PricingIntegration.SparseCounter
open Ramsey61.DenseCounter
open PricingIntegration.FoldedThreshold

def offset (height row : Nat) : Nat :=
  ∑ i ∈ Finset.range row, min (i + 1) height

theorem offset_succ (height row : Nat) :
    offset height (row + 1) = offset height row + min (row + 1) height := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (height : Nat) : Monotone (offset height) := by
  apply monotone_nat_of_le_succ
  intro row
  rw [offset_succ]
  omega

def atom (start height row column : Nat) := start + offset height row + column

theorem atom_injective (start height r c r' c' : Nat)
    (hc : c < min (r + 1) height) (hc' : c' < min (r' + 1) height)
    (heq : atom start height r c = atom start height r' c') :
    r = r' ∧ c = c' := by
  have hrow : r = r' := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hnext := offset_mono height (show r + 1 ≤ r' by omega)
      rw [offset_succ] at hnext
      unfold atom at heq
      omega
    · have hnext := offset_mono height (show r' + 1 ≤ r by omega)
      rw [offset_succ] at hnext
      unfold atom at heq
      omega
  refine ⟨hrow, ?_⟩
  subst r'
  unfold atom at heq
  omega

abbrev Cell (rows height : Nat) :=
  {p : Fin rows × Fin height // p.2.val ≤ p.1.val}

def cellAtom (start : Nat) {rows height : Nat} (p : Cell rows height) : Nat :=
  atom start height p.1.1.val p.1.2.val

theorem cellAtom_injective (start rows height : Nat) :
    Function.Injective (@cellAtom start rows height) := by
  intro p q heq
  obtain ⟨hr, hc⟩ := atom_injective start height p.1.1.val p.1.2.val
    q.1.1.val q.1.2.val
    (by omega) (by omega) heq
  apply Subtype.ext
  exact Prod.ext (Fin.ext hr) (Fin.ext hc)

def prefixCountSigned (v : Valuation) (xs : List Lit) (n : Nat) := count v (xs.take n)

theorem prefixCountSigned_succ (v : Valuation) (xs : List Lit) (row : Nat)
    (hr : row < xs.length) :
    prefixCountSigned v xs (row + 1) = prefixCountSigned v xs row + if value v xs[row] then 1 else 0 := by
  unfold prefixCountSigned count
  rw [← List.take_concat_get hr, List.concat_eq_append, List.countP_append,
    List.countP_singleton]

noncomputable def extend (v : Valuation) (xs : List Lit) (start height : Nat) : Valuation :=
  fun a => if h : ∃ p : Cell xs.length height, cellAtom start p = a then
    let p := Classical.choose h
    decide (p.1.2.val + 1 ≤ prefixCountSigned v xs (p.1.1.val + 1))
  else v a

theorem extend_at_cell (v : Valuation) (xs : List Lit) (start height : Nat)
    (p : Cell xs.length height) :
    extend v xs start height (cellAtom start p) =
      decide (p.1.2.val + 1 ≤ prefixCountSigned v xs (p.1.1.val + 1)) := by
  have hex : ∃ q : Cell xs.length height, cellAtom start q = cellAtom start p := ⟨p, rfl⟩
  rw [extend, dif_pos hex]
  have heq : Classical.choose hex = p :=
    cellAtom_injective start xs.length height (Classical.choose_spec hex)
  simp only [heq]

theorem extend_before_start (v : Valuation) (xs : List Lit) (start height a : Nat)
    (ha : a < start) : extend v xs start height a = v a := by
  have hn : ¬∃ p : Cell xs.length height, cellAtom start p = a := by
    rintro ⟨p, hp⟩
    unfold cellAtom atom at hp
    omega
  rw [extend, dif_neg hn]

def threshold (start height i j : Nat) : Signal :=
  if j = 0 then .constant true
  else if i < j then .constant false
  else .literal (true, atom start height (i - 1) (j - 1))

theorem holds_threshold (v : Valuation) (xs : List Lit) (start height i j : Nat)
    (hi : i ≤ xs.length) (hj : j ≤ height) :
    Holds (extend v xs start height) (threshold start height i j) ↔
      j ≤ prefixCountSigned v xs i := by
  have hb : prefixCountSigned v xs i ≤ i :=
    le_trans List.countP_le_length (List.length_take_le _ _)
  by_cases hz : j = 0
  · simp [threshold, hz, Holds]
  by_cases hij : i < j
  · simp [threshold, hz, hij, Holds]
    omega
  have hp : j - 1 ≤ i - 1 := by omega
  let p : Cell xs.length height :=
    ⟨(⟨i - 1, by omega⟩, ⟨j - 1, by omega⟩), hp⟩
  rw [threshold, if_neg hz, if_neg hij]
  change extend v xs start height (cellAtom start p) = true ↔ _
  rw [extend_at_cell]
  have hi' : i - 1 + 1 = i := by omega
  have hj' : j - 1 + 1 = j := by omega
  simp only [p, hi', hj', decide_eq_true_eq]

def cell (xs : List Lit) (start height row column : Nat) : List (List Signal) :=
  recurrenceClauses
    (threshold start height (row + 1) (column + 1))
    (threshold start height row (column + 1))
    (threshold start height row column)
    (.literal (xs[row]?.getD (true, 0)))

theorem cell_satisfied (v : Valuation) (xs : List Lit) (start height row column : Nat)
    (hinputs : ∀ l ∈ xs, l.2 < start)
    (hr : row < xs.length) (hc : column < min (row + 1) height) :
    SignalFormulaSat (extend v xs start height) (cell xs start height row column) := by
  rw [cell, recurrenceClauses_sat_iff]
  rw [holds_threshold v xs start height _ _ (by omega) (by omega),
    holds_threshold v xs start height _ _ (by omega) (by omega),
    holds_threshold v xs start height _ _ (by omega) (by omega)]
  simp only [Holds, List.getElem?_eq_getElem hr, Option.getD_some]
  rw [extend_before_start v xs start height _ (hinputs _ (List.getElem_mem hr)),
    prefixCountSigned_succ v xs row hr]
  by_cases heq : v xs[row].2 = xs[row].1
  · simp [value, heq]
    omega
  · simp [value, heq]

def signals (xs : List Lit) (start height : Nat) : List (List Signal) :=
  (List.range xs.length).flatMap fun row =>
    (List.range (min (row + 1) height)).flatMap fun column =>
      cell xs start height row column

/-- The exact triangular four-clause counter has a constructed satisfying
extension preserving every earlier variable. No Realizes premise remains. -/
theorem sparseCounter_satisfying_extension
    (v : Valuation) (xs : List Lit) (start height : Nat)
    (hinputs : ∀ l ∈ xs, l.2 < start) :
    ∃ w : Valuation, (∀ a < start, w a = v a) ∧
      FormulaSat w (normalizeFormula (signals xs start height)) ∧
      (∀ i ≤ xs.length, ∀ j ≤ height,
        Holds w (threshold start height i j) ↔ j ≤ prefixCountSigned v xs i) := by
  refine ⟨extend v xs start height,
    fun a ha => extend_before_start v xs start height a ha, ?_, ?_⟩
  · apply normalizeFormula_sound
    intro cl hcl
    simp only [signals, List.mem_flatMap] at hcl
    obtain ⟨row, hr, col, hc, hm⟩ := hcl
    exact cell_satisfied v xs start height row col hinputs
      (List.mem_range.mp hr) (List.mem_range.mp hc) cl hm
  · exact fun i hi j hj => holds_threshold v xs start height i j hi hj

#print axioms sparseCounter_satisfying_extension
end PricingIntegration.SparseCounter
