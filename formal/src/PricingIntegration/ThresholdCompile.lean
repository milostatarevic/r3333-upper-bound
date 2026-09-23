import PricingIntegration.SparseCounter

namespace PricingIntegration.ThresholdCompile
open Ramsey61.DenseCounter
open PricingIntegration.FoldedThreshold

def emitted (k : Known) (xs : List Lit) (target start : Nat) : CNF :=
  if target ≤ trueFixed k xs then []
  else if (unknown k xs).length < target - trueFixed k xs then []
  else normalizeFormula (SparseCounter.signals (unknown k xs) start (target - trueFixed k xs))

def top (k : Known) (xs : List Lit) (target start : Nat) : Signal :=
  if target ≤ trueFixed k xs then .constant true
  else if (unknown k xs).length < target - trueFixed k xs then .constant false
  else SparseCounter.threshold start (target - trueFixed k xs)
    (unknown k xs).length (target - trueFixed k xs)

/-- Prefix-constant folding and the producer's sparse allocation are proved
together for signed literals. The witness preserves every existing atom and
represents the exact original count, including omitted true constants. -/
theorem threshold_compiler_extension
    (v : Valuation) (k : Known) (hk : Sound v k) (xs : List Lit)
    (target start : Nat) (hinputs : ∀ l ∈ xs, l.2 < start) :
    ∃ w : Valuation, (∀ a < start, w a = v a) ∧
      FormulaSat w (emitted k xs target start) ∧
      (Holds w (top k xs target start) ↔ target ≤ count v xs) := by
  have hfold := folded_threshold_iff v k hk xs target
  by_cases ht : target ≤ trueFixed k xs
  · refine ⟨v, fun _ _ => rfl, ?_, ?_⟩
    · simp [emitted, ht, FormulaSat]
    · simpa [top, ht, Holds] using hfold.symm
  by_cases hu : (unknown k xs).length < target - trueFixed k xs
  · refine ⟨v, fun _ _ => rfl, ?_, ?_⟩
    · simp [emitted, ht, hu, FormulaSat]
    · simpa [top, ht, hu, Holds] using hfold.symm
  obtain ⟨w, hw, hf, hsig⟩ := SparseCounter.sparseCounter_satisfying_extension
    v (unknown k xs) start (target - trueFixed k xs)
    (fun l hl => hinputs l (List.mem_of_mem_filter hl))
  refine ⟨w, hw, ?_, ?_⟩
  · simpa [emitted, ht, hu] using hf
  · simp only [top, ht, hu, if_false]
    rw [hsig _ (le_refl _) _ (le_refl _)]
    simpa only [ht, hu, if_false, SparseCounter.prefixCountSigned, List.take_length] using hfold.symm

def Below (f : CNF) (start : Nat) : Prop :=
  ∀ clause ∈ f, ∀ literal ∈ clause, literal.2 < start

theorem preserves_prior_formula (v w : Valuation) (start : Nat) (f : CNF)
    (hw : ∀ a < start, w a = v a) (hb : Below f start) (hf : FormulaSat v f) :
    FormulaSat w f := by
  intro clause hc
  obtain ⟨literal, hl, hsat⟩ := hf clause hc
  exact ⟨literal, hl, (hw literal.2 (hb clause hc literal hl)).trans hsat⟩

/-- Every generated threshold can be appended to the actual already satisfied
prefix. This is the induction step needed by the full A/B encoder. -/
theorem threshold_compiler_preserves_prefix
    (v : Valuation) (k : Known) (hk : Sound v k) (xs : List Lit)
    (target start : Nat) (hinputs : ∀ l ∈ xs, l.2 < start)
    (base : CNF) (hbase : FormulaSat v base) (hbelow : Below base start) :
    ∃ w : Valuation, (∀ a < start, w a = v a) ∧
      FormulaSat w (base ++ emitted k xs target start) ∧
      (Holds w (top k xs target start) ↔ target ≤ count v xs) := by
  obtain ⟨w, hw, hf, ht⟩ := threshold_compiler_extension v k hk xs target start hinputs
  exact ⟨w, hw, formulaSat_append w base _ |>.mpr
    ⟨preserves_prior_formula v w start base hw hbelow hbase, hf⟩, ht⟩

#print axioms threshold_compiler_preserves_prefix

def boundSignal (upper : Bool) (s : Signal) : Signal := if upper then negate s else s

def boundClause (gate : Option Nat) (s : Signal) : List Signal :=
  match gate with
  | none => [s]
  | some g => [.literal (false, g), s]

def boundHolds (v : Valuation) (xs : List Lit) (limit : Nat)
    (upper : Bool) (gate : Option Nat) : Prop :=
  (∀ g ∈ gate, v g = true) → if upper then count v xs ≤ limit else limit ≤ count v xs

/-- The actual optional highness gate and upper/lower final clause preserve
the physical meaning of the folded sparse threshold. -/
theorem bound_compiler_satisfies_prefix
    (v : Valuation) (k : Known) (hk : Sound v k) (xs : List Lit)
    (limit start : Nat) (upper : Bool) (gate : Option Nat)
    (hinputs : ∀ l ∈ xs, l.2 < start) (hgate : ∀ g ∈ gate, g < start)
    (hb : boundHolds v xs limit upper gate)
    (base : CNF) (hbase : FormulaSat v base) (hbelow : Below base start) :
    ∃ w : Valuation, (∀ a < start, w a = v a) ∧
      FormulaSat w
        ((base ++ emitted k xs (limit + if upper then 1 else 0) start) ++
          normalizeFormula [boundClause gate (boundSignal upper
            (top k xs (limit + if upper then 1 else 0) start))]) := by
  obtain ⟨w, hw, hf, ht⟩ := threshold_compiler_preserves_prefix v k hk xs
    (limit + if upper then 1 else 0) start hinputs base hbase hbelow
  refine ⟨w, hw, (formulaSat_append _ _ _).mpr ⟨hf, ?_⟩⟩
  apply normalizeFormula_sound
  simp only [SignalFormulaSat, List.mem_singleton, forall_eq]
  have hvalue : Holds w (boundSignal upper (top k xs (limit + if upper then 1 else 0) start)) ↔
      (if upper then count v xs ≤ limit else limit ≤ count v xs) := by
    cases upper
    · simpa [boundSignal] using ht
    · simp only [boundSignal, if_true, holds_negate]
      simp only [Bool.true_eq, ↓reduceIte] at ht
      rw [ht]
      omega
  cases gate with
  | none =>
    simp only [boundClause, SignalClauseSat, List.mem_singleton, exists_eq_left]
    exact hvalue.mpr (hb (by simp))
  | some g =>
    by_cases hg : v g = true
    · have hbound := hb (by simpa using hg)
      exact ⟨_, by simp [boundClause], hvalue.mpr hbound⟩
    · refine ⟨.literal (false, g), by simp [boundClause], ?_⟩
      change w g = false
      rw [hw g (hgate g (by simp))]
      exact Bool.eq_false_iff.mpr hg

#print axioms bound_compiler_satisfies_prefix
end PricingIntegration.ThresholdCompile
