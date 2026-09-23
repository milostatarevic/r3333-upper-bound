import Mathlib.Data.List.Count
import Mathlib.Tactic

/-!
# The exact four-clause dense counters used by the C encoder

`encode.py` emits full equivalences, not the older one-way at-most counter.
This module proves a forward satisfying-assignment theorem for those four
clauses, including their constant boundaries and the producer's ordered
constant/duplicate/tautology normalization. Literal and CNF types are
identical to the Boolean types at the current Ramsey61 endpoint; this module
has no dependency on that endpoint, avoiding an import cycle.
-/

namespace Ramsey61.DenseCounter

abbrev Literal := Bool × Nat
abbrev CNF := List (List Literal)
abbrev Valuation := Nat → Bool

def ClauseSat (v : Valuation) (clause : List Literal) : Prop :=
  ∃ literal ∈ clause, v literal.2 = literal.1

def FormulaSat (v : Valuation) (formula : CNF) : Prop :=
  ∀ clause ∈ formula, ClauseSat v clause

inductive Signal where
  | constant : Bool → Signal
  | literal : Literal → Signal
  deriving DecidableEq

def Holds (v : Valuation) : Signal → Prop
  | .constant b => b = true
  | .literal literal => v literal.2 = literal.1

def flip (literal : Literal) : Literal := (!literal.1, literal.2)

def negate : Signal → Signal
  | .constant b => .constant (!b)
  | .literal literal => .literal (flip literal)

@[simp] theorem holds_negate (v : Valuation) (signal : Signal) :
    Holds v (negate signal) ↔ ¬ Holds v signal := by
  cases signal with
  | constant b => cases b <;> simp [Holds, negate]
  | literal literal =>
    rcases literal with ⟨sign, atom⟩
    cases sign <;> cases h : v atom <;> simp [Holds, negate, flip, h]

def SignalClauseSat (v : Valuation) (clause : List Signal) : Prop :=
  ∃ signal ∈ clause, Holds v signal

def SignalFormulaSat (v : Valuation) (formula : List (List Signal)) : Prop :=
  ∀ clause ∈ formula, SignalClauseSat v clause

/-- The four tuples in `encode.recurrence_clauses`, in their original order. -/
def recurrenceClauses (target previous incoming lower : Signal) : List (List Signal) :=
  [[negate previous, target],
   [negate incoming, negate lower, target],
   [negate target, previous, incoming],
   [negate target, previous, lower]]

theorem recurrenceClauses_sat_iff (v : Valuation)
    (target previous incoming lower : Signal) :
    SignalFormulaSat v (recurrenceClauses target previous incoming lower) ↔
      (Holds v target ↔ Holds v previous ∨ Holds v incoming ∧ Holds v lower) := by
  simp [SignalFormulaSat, recurrenceClauses, SignalClauseSat]
  tauto

/-- Accumulator form of `normalized_clause`: preserve first occurrence order,
fold Boolean constants, and omit a clause containing complementary literals.
`none` is an omitted tautological clause, whereas `some []` is an empty clause. -/
def normalizeAux (seen : List Literal) : List Signal → Option (List Literal)
  | [] => some seen
  | .constant true :: _ => none
  | .constant false :: rest => normalizeAux seen rest
  | .literal literal :: rest =>
      if flip literal ∈ seen then none
      else if literal ∈ seen then normalizeAux seen rest
      else normalizeAux (seen ++ [literal]) rest

def OptionClauseSat (v : Valuation) : Option (List Literal) → Prop
  | none => True
  | some clause => ClauseSat v clause

theorem normalizeAux_sound (v : Valuation) (signals : List Signal) :
    ∀ seen, ClauseSat v seen ∨ SignalClauseSat v signals →
      OptionClauseSat v (normalizeAux seen signals) := by
  induction signals with
  | nil =>
    intro seen h
    simpa [normalizeAux, OptionClauseSat, SignalClauseSat] using h
  | cons signal rest ih =>
    intro seen h
    have hsplit : ClauseSat v seen ∨ Holds v signal ∨ SignalClauseSat v rest := by
      simpa [SignalClauseSat, List.mem_cons] using h
    cases signal with
    | constant b =>
      cases b
      · apply ih seen
        simpa [Holds] using hsplit
      · trivial
    | literal literal =>
      simp only [normalizeAux]
      split_ifs with hflip hmem
      · trivial
      · apply ih seen
        rcases hsplit with hs | hl | hr
        · exact Or.inl hs
        · exact Or.inl ⟨literal, hmem, hl⟩
        · exact Or.inr hr
      · apply ih (seen ++ [literal])
        rcases hsplit with hs | hl | hr
        · rcases hs with ⟨l, hls, htrue⟩
          exact Or.inl ⟨l, List.mem_append_left _ hls, htrue⟩
        · exact Or.inl ⟨literal, by simp, hl⟩
        · exact Or.inr hr

def normalizeClause (signals : List Signal) : Option (List Literal) :=
  normalizeAux [] signals

def normalizeFormula (formula : List (List Signal)) : CNF :=
  formula.filterMap normalizeClause

theorem normalizeFormula_sound (v : Valuation) (formula : List (List Signal))
    (h : SignalFormulaSat v formula) : FormulaSat v (normalizeFormula formula) := by
  intro clause hclause
  obtain ⟨signals, hmem, heq⟩ := List.mem_filterMap.mp hclause
  have hs := normalizeAux_sound v signals [] (Or.inr (h signals hmem))
  change OptionClauseSat v (normalizeClause signals) at hs
  simpa [heq, OptionClauseSat] using hs

@[simp] theorem normalizeFormula_append (first second : List (List Signal)) :
    normalizeFormula (first ++ second) = normalizeFormula first ++ normalizeFormula second := by
  simp [normalizeFormula]

@[simp] theorem formulaSat_append (v : Valuation) (first second : CNF) :
    FormulaSat v (first ++ second) ↔ FormulaSat v first ∧ FormulaSat v second := by
  simp [FormulaSat, or_imp, forall_and]

/-- Actual count of true input occurrences in a prefixLen, in the producer's order. -/
def prefixCount (v : Valuation) (inputs : List Nat) (length : Nat) : Nat :=
  List.countP v (inputs.take length)

@[simp] theorem prefixCount_zero (v : Valuation) (inputs : List Nat) :
    prefixCount v inputs 0 = 0 := by simp [prefixCount]

theorem prefixCount_succ (v : Valuation) (inputs : List Nat) (row : Nat)
    (hrow : row < inputs.length) :
    prefixCount v inputs (row + 1) = prefixCount v inputs row +
      (if v inputs[row] then 1 else 0) := by
  unfold prefixCount
  rw [← List.take_concat_get hrow, List.concat_eq_append, List.countP_append,
    List.countP_singleton]

/-- Zero-based row and column; column j denotes threshold j+1. -/
def denseAtom (start height row column : Nat) : Nat :=
  start + (row * height + column)

/-- Prefix 0 and threshold 0 are constants, exactly as in `emit_counter`. -/
def thresholdSignal (start height prefixLen threshold : Nat) : Signal :=
  if threshold = 0 then .constant true
  else if prefixLen = 0 then .constant false
  else .literal (true, denseAtom start height (prefixLen - 1) (threshold - 1))

/-- A valuation realizes this rectangle using actual counts of its input bits. -/
def Realizes (v : Valuation) (inputs : List Nat) (start height : Nat) : Prop :=
  ∀ row < inputs.length, ∀ column < height,
    v (denseAtom start height row column) =
      decide (column + 1 ≤ prefixCount v inputs (row + 1))

theorem holds_thresholdSignal (v : Valuation) (inputs : List Nat)
    (start height : Nat) (h : Realizes v inputs start height)
    (prefixLen threshold : Nat) (hp : prefixLen ≤ inputs.length) (ht : threshold ≤ height) :
    Holds v (thresholdSignal start height prefixLen threshold) ↔
      threshold ≤ prefixCount v inputs prefixLen := by
  by_cases hz : threshold = 0
  · simp [thresholdSignal, hz, Holds]
  by_cases hpz : prefixLen = 0
  · simp [thresholdSignal, hz, hpz, Holds]
  have hrow : prefixLen - 1 < inputs.length := by omega
  have hcol : threshold - 1 < height := by omega
  have hv := h (prefixLen - 1) hrow (threshold - 1) hcol
  have ep : prefixLen - 1 + 1 = prefixLen := by omega
  have et : threshold - 1 + 1 = threshold := by omega
  simp only [thresholdSignal, hz, hpz, ↓reduceIte, Holds, hv, ep, et,
    decide_eq_true_eq]

/-- One emitted row/column recurrence, with boundary constants folded later. -/
def counterCell (inputs : List Nat) (start height row column : Nat) : List (List Signal) :=
  recurrenceClauses
    (thresholdSignal start height (row + 1) (column + 1))
    (thresholdSignal start height row (column + 1))
    (.literal (true, inputs[row]?.getD 0))
    (thresholdSignal start height row column)

theorem counterCell_sat (v : Valuation) (inputs : List Nat) (start height : Nat)
    (h : Realizes v inputs start height) (row column : Nat)
    (hrow : row < inputs.length) (hcolumn : column < height) :
    SignalFormulaSat v (counterCell inputs start height row column) := by
  rw [counterCell, recurrenceClauses_sat_iff]
  rw [holds_thresholdSignal v inputs start height h _ _ (by omega) (by omega),
    holds_thresholdSignal v inputs start height h _ _ (by omega) (by omega),
    holds_thresholdSignal v inputs start height h _ _ (by omega) (by omega)]
  simp only [Holds, List.getElem?_eq_getElem hrow, Option.getD_some]
  rw [prefixCount_succ v inputs row hrow]
  cases v inputs[row] <;> simp
  omega

/-- Exact row-major counter generation: all columns, including unreachable ones. -/
def counterSignals (inputs : List Nat) (start height : Nat) : List (List Signal) :=
  (List.range inputs.length).flatMap fun row =>
    (List.range height).flatMap fun column => counterCell inputs start height row column

def counterCNF (inputs : List Nat) (start height : Nat) : CNF :=
  normalizeFormula (counterSignals inputs start height)

theorem counterCNF_satisfied_of_realizes (v : Valuation) (inputs : List Nat)
    (start height : Nat) (h : Realizes v inputs start height) :
    FormulaSat v (counterCNF inputs start height) := by
  apply normalizeFormula_sound
  intro clause hclause
  simp only [counterSignals, List.mem_flatMap] at hclause
  obtain ⟨row, hrow, column, hcolumn, hcell⟩ := hclause
  exact counterCell_sat v inputs start height h row column
    (List.mem_range.mp hrow) (List.mem_range.mp hcolumn) clause hcell


/-- The exact contiguous namespace allocated to one dense counter. -/
def InRectangle (start rows height atom : Nat) : Prop :=
  start ≤ atom ∧ atom < start + rows * height

instance (start rows height atom : Nat) : Decidable (InRectangle start rows height atom) :=
  inferInstanceAs (Decidable (start ≤ atom ∧ atom < start + rows * height))

theorem denseAtom_inRectangle (start rows height row column : Nat)
    (hrow : row < rows) (hcolumn : column < height) :
    InRectangle start rows height (denseAtom start height row column) := by
  constructor
  · simp [denseAtom]
  · have hbound : row * height + column < rows * height := calc
      row * height + column < row * height + height := Nat.add_lt_add_left hcolumn _
      _ = (row + 1) * height := by simp [Nat.add_mul]
      _ ≤ rows * height := Nat.mul_le_mul_right height (by omega)
    simpa [denseAtom] using Nat.add_lt_add_left hbound start

/-- Extend a valuation by the actual prefix counts of its original input bits.
Only the allocated rectangle changes. Height zero has an empty rectangle. -/
def extend (v : Valuation) (inputs : List Nat) (start height : Nat) : Valuation :=
  fun atom => if InRectangle start inputs.length height atom then
    decide ((atom - start) % height + 1 ≤
      prefixCount v inputs ((atom - start) / height + 1))
  else v atom

theorem extend_eq_of_outside (v : Valuation) (inputs : List Nat)
    (start height atom : Nat) (h : ¬ InRectangle start inputs.length height atom) :
    extend v inputs start height atom = v atom := by
  simp [extend, h]

theorem extend_denseAtom (v : Valuation) (inputs : List Nat)
    (start height row column : Nat)
    (hrow : row < inputs.length) (hcolumn : column < height) :
    extend v inputs start height (denseAtom start height row column) =
      decide (column + 1 ≤ prefixCount v inputs (row + 1)) := by
  have hrange := denseAtom_inRectangle start inputs.length height row column hrow hcolumn
  have hheight : 0 < height := by omega
  have hdiv : (row * height + column) / height = row := by
    rw [Nat.mul_comm row height, Nat.mul_add_div hheight, Nat.div_eq_of_lt hcolumn]
    simp
  have hmod : (row * height + column) % height = column :=
    Nat.mul_add_mod_of_lt hcolumn
  rw [extend, if_pos hrange]
  simp [denseAtom, hdiv, hmod]

def InputsOutside (inputs : List Nat) (start height : Nat) : Prop :=
  ∀ atom ∈ inputs, ¬ InRectangle start inputs.length height atom

theorem prefixCount_congr (v w : Valuation) (inputs : List Nat)
    (h : ∀ atom ∈ inputs, v atom = w atom) (length : Nat) :
    prefixCount v inputs length = prefixCount w inputs length := by
  apply List.countP_congr
  intro atom hmem
  rw [h atom (List.mem_of_mem_take hmem)]

theorem extend_realizes (v : Valuation) (inputs : List Nat) (start height : Nat)
    (hout : InputsOutside inputs start height) :
    Realizes (extend v inputs start height) inputs start height := by
  intro row hrow column hcolumn
  rw [extend_denseAtom v inputs start height row column hrow hcolumn]
  have hcounts := prefixCount_congr (extend v inputs start height) v inputs
    (fun atom hmem => extend_eq_of_outside v inputs start height atom (hout atom hmem))
    (row + 1)
  rw [hcounts]

/-- Existing physical clauses or prior auxiliary clauses mention no atom of
this new counter rectangle. This is the preservation condition, not an axiom. -/
def FormulaOutside (base : CNF) (start rows height : Nat) : Prop :=
  ∀ clause ∈ base, ∀ literal ∈ clause, ¬ InRectangle start rows height literal.2

theorem extend_preserves_formula (v : Valuation) (inputs : List Nat)
    (start height : Nat) (base : CNF)
    (hout : FormulaOutside base start inputs.length height) (hbase : FormulaSat v base) :
    FormulaSat (extend v inputs start height) base := by
  intro clause hclause
  obtain ⟨literal, hmem, htrue⟩ := hbase clause hclause
  refine ⟨literal, hmem, ?_⟩
  rw [extend_eq_of_outside v inputs start height literal.2 (hout clause hclause literal hmem)]
  exact htrue

/-- The fully constructed threshold valuation satisfies the exact normalized
four-clause dense counter and preserves every clause outside its namespace. -/
theorem extend_satisfies_base_and_counter (v : Valuation) (inputs : List Nat)
    (start height : Nat) (base : CNF)
    (hinputs : InputsOutside inputs start height)
    (hout : FormulaOutside base start inputs.length height) (hbase : FormulaSat v base) :
    FormulaSat (extend v inputs start height) (base ++ counterCNF inputs start height) := by
  rw [formulaSat_append]
  exact ⟨extend_preserves_formula v inputs start height base hout hbase,
    counterCNF_satisfied_of_realizes _ inputs start height (extend_realizes v inputs start height hinputs)⟩

/-- An existential interface directly compatible with the current Boolean CNF
endpoint. The witness also states agreement outside the new rectangle. -/
theorem exists_satisfying_extension (v : Valuation) (inputs : List Nat)
    (start height : Nat) (base : CNF)
    (hinputs : InputsOutside inputs start height)
    (hout : FormulaOutside base start inputs.length height) (hbase : FormulaSat v base) :
    ∃ w : Valuation,
      (∀ atom, ¬ InRectangle start inputs.length height atom → w atom = v atom) ∧
      FormulaSat w (base ++ counterCNF inputs start height) := by
  refine ⟨extend v inputs start height, ?_,
    extend_satisfies_base_and_counter v inputs start height base hinputs hout hbase⟩
  exact fun atom h => extend_eq_of_outside v inputs start height atom h


end Ramsey61.DenseCounter
