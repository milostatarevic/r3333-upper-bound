import R4333Lean.ClebschCompletionCNF
import R4333Lean.ColorRelabel

/-!
# Semantics of the Clebsch-complement exhaustion certificate

This file connects a mathematical three-colouring whose zero-colour graph is
the canonical Clebsch graph to the exact eighty Boolean variables in
`ClebschCompletionCNF`.
-/

namespace R4333

open FiniteColorCNF

private theorem list_getD_eq_getElem_of_lt {A : Type*}
    (l : List A) (fallback : A) {i : Nat} (hi : i < l.length) :
    l.getD i fallback = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Interpret an in-range natural as a vertex of `Fin 16`.  Every use below
comes from the explicit complement-edge list, whose entries are in range. -/
def fin16OfNat (a : Nat) : Fin 16 :=
  ⟨a % 16, Nat.mod_lt _ (by decide)⟩

/-- The actual Boolean completion vector of a colouring: `true` means colour
one and `false` means colour two. -/
def clebschCompletionBits (d : EdgeColoring (Fin 16) ThreeColor) : List Bool :=
  clebschComplementEdges.map fun e =>
    decide (d (fin16OfNat e.1) (fin16OfNat e.2) = (1 : ThreeColor))

/-- Turn the completion vector into the valuation expected by the CNF. -/
def clebschCompletionValuation
    (d : EdgeColoring (Fin 16) ThreeColor) : Sat.Valuation := fun i =>
  (clebschCompletionBits d).getD i false = true

theorem clebschComplementEdges_eq_filter :
    clebschComplementEdges =
      (edges 16).filter fun e => canonicalClebschRed e.1 e.2 = false := by
  decide

theorem clebschComplementEdges_length : clebschComplementEdges.length = 80 := by
  decide

set_option maxRecDepth 100000 in
theorem clebschDecomposition_lengths :
    ∀ bits ∈ clebschDecompositions, bits.length = 80 := by
  decide

theorem pair_mem_clebschComplementEdges
    {a b : Nat} (ha : a < 16) (hb : b < 16) (hab : a < b)
    (hred : canonicalClebschRed a b = false) :
    (a, b) ∈ clebschComplementEdges := by
  rw [clebschComplementEdges_eq_filter]
  exact List.mem_filter.mpr
    ⟨mem_edges_of_bounds ha hb hab, by simp [hred]⟩

@[simp] theorem fin16OfNat_eq {a : Nat} (ha : a < 16) :
    fin16OfNat a = ⟨a, ha⟩ := by
  apply Fin.ext
  simp [fin16OfNat, Nat.mod_eq_of_lt ha]

/-- On every canonical non-red edge, the Boolean variable has exactly its
mathematical colour-one meaning. -/
theorem clebschCompletionValuation_edge
    (d : EdgeColoring (Fin 16) ThreeColor)
    {a b : Nat} (ha : a < 16) (hb : b < 16) (hab : a < b)
    (hred : canonicalClebschRed a b = false) :
    clebschCompletionValuation d (clebschComplementIndex a b) ↔
      d ⟨a, ha⟩ ⟨b, hb⟩ = (1 : ThreeColor) := by
  have hmem : (a, b) ∈ clebschComplementEdges :=
    pair_mem_clebschComplementEdges ha hb hab hred
  have hidx : clebschComplementIndex a b < clebschComplementEdges.length := by
    simpa [clebschComplementIndex, min_eq_left (Nat.le_of_lt hab),
      max_eq_right (Nat.le_of_lt hab)] using
      (List.idxOf_lt_length_iff.mpr hmem)
  have hget :
      clebschComplementEdges[clebschComplementIndex a b]'hidx = (a, b) := by
    have hindex : clebschComplementIndex a b =
        clebschComplementEdges.idxOf (a, b) := by
      simp [clebschComplementIndex, min_eq_left (Nat.le_of_lt hab),
        max_eq_right (Nat.le_of_lt hab)]
    calc
      clebschComplementEdges[clebschComplementIndex a b]'hidx =
          clebschComplementEdges[clebschComplementEdges.idxOf (a, b)]'(
            hindex ▸ hidx) := getElem_congr_idx hindex
      _ = (a, b) := List.idxOf_get (hindex ▸ hidx)
  have hidxMap :
      clebschComplementIndex a b <
        (clebschComplementEdges.map fun e =>
          decide (d (fin16OfNat e.1) (fin16OfNat e.2) = (1 : ThreeColor))).length := by
    simpa using hidx
  simp only [clebschCompletionValuation, clebschCompletionBits]
  rw [list_getD_eq_getElem_of_lt _ _ hidxMap, List.getElem_map, hget]
  simp [fin16OfNat_eq ha, fin16OfNat_eq hb]

/-- A vector different from an eighty-bit row satisfies the clause which
blocks that row. -/
theorem valuation_satisfies_completionBlocker
    (actual bits : List Bool)
    (hactual : actual.length = 80) (hbits : bits.length = 80)
    (hne : actual ≠ bits) :
    Sat.Valuation.satisfies
      ((fun i => actual.getD i false = true) : Sat.Valuation)
      (clebschCompletionBlocker bits) := by
  have hdiff : ∃ i < 80, actual.getD i false ≠ bits.getD i false := by
    by_contra h
    push Not at h
    apply hne
    apply List.ext_get_iff.mpr
    refine ⟨hactual.trans hbits.symm, ?_⟩
    intro n hnActual hnBits
    have hn : n < 80 := by simpa [hactual] using hnActual
    have heq := h n hn
    rw [list_getD_eq_getElem_of_lt _ _ hnActual,
      list_getD_eq_getElem_of_lt _ _ hnBits] at heq
    exact heq
  obtain ⟨i, hi, hdiff⟩ := hdiff
  by_cases hbit : bits.getD i false = true
  · apply FiniteColorCNF.satisfies_of_mem_holds (l := Sat.Literal.neg i)
    · simp only [clebschCompletionBlocker]
      apply List.mem_map.mpr
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      have hbit' : bits[i]?.getD false = true := by
        simpa only [List.getD_eq_getElem?_getD] using hbit
      simp [hbit']
    · change ¬(actual.getD i false = true)
      intro hactualBit
      exact hdiff (hactualBit.trans hbit.symm)
  · have hbitFalse : bits.getD i false = false := by
      cases h : bits.getD i false <;> simp_all
    have hactualTrue : actual.getD i false = true := by
      cases h : actual.getD i false <;> simp_all
    apply FiniteColorCNF.satisfies_of_mem_holds (l := Sat.Literal.pos i)
    · simp only [clebschCompletionBlocker]
      apply List.mem_map.mpr
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      have hbitFalse' : bits[i]?.getD false = false := by
        simpa only [List.getD_eq_getElem?_getD] using hbitFalse
      simp [hbitFalse']
    · exact hactualTrue

/-- The zero-colour graph of `d` is exactly the fixed canonical Clebsch
graph, away from the irrelevant diagonal. -/
def HasCanonicalClebschZero
    (d : EdgeColoring (Fin 16) ThreeColor) : Prop :=
  ∀ a b, a ≠ b →
    (d a b = (0 : ThreeColor) ↔
      canonicalClebschRed a.val b.val = true)

private theorem fin3_eq_two_of_ne_zero_ne_one
    (q : ThreeColor) (h0 : q ≠ 0) (h1 : q ≠ 1) : q = 2 := by
  fin_cases q <;> simp_all

private theorem canonical_nonred_ne_zero
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hcanonical : HasCanonicalClebschZero d)
    {a b : Nat} (ha : a < 16) (hb : b < 16) (hab : a < b)
    (hred : canonicalClebschRed a b = false) :
    d ⟨a, ha⟩ ⟨b, hb⟩ ≠ (0 : ThreeColor) := by
  intro hzero
  have htrue := (hcanonical ⟨a, ha⟩ ⟨b, hb⟩ (Fin.ne_of_lt hab)).mp hzero
  simp [hred] at htrue

/-- Every good colouring with the fixed zero graph satisfies all 320 NAE
triangle clauses of the completion CNF. -/
theorem coloring_satisfies_clebschCompletionTriangles
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d)
    (hcanonical : HasCanonicalClebschZero d) :
    (clebschCompletionValuation d).satisfies_fmla
      ((triples 16).flatMap clebschCompletionTripleClauses) := by
  constructor
  intro clause hclause
  simp only [List.mem_flatMap] at hclause
  obtain ⟨⟨a, b, c⟩, htriple, hclause⟩ := hclause
  obtain ⟨ha, hb, hc, hab, hbc⟩ := mem_triples_iff_bounds htriple
  have hac : a < c := hab.trans hbc
  simp only [clebschCompletionTripleClauses] at hclause
  split at hclause
  · simp at hclause
  · rename_i hnonred
    have hredAB : canonicalClebschRed a b = false := by
      cases h : canonicalClebschRed a b <;> simp_all
    have hredAC : canonicalClebschRed a c = false := by
      cases h : canonicalClebschRed a c <;> simp_all
    have hredBC : canonicalClebschRed b c = false := by
      cases h : canonicalClebschRed b c <;> simp_all
    have hAB := clebschCompletionValuation_edge d ha hb hab hredAB
    have hAC := clebschCompletionValuation_edge d ha hc hac hredAC
    have hBC := clebschCompletionValuation_edge d hb hc hbc hredBC
    have hn0AB := canonical_nonred_ne_zero d hcanonical ha hb hab hredAB
    have hn0AC := canonical_nonred_ne_zero d hcanonical ha hc hac hredAC
    have hn0BC := canonical_nonred_ne_zero d hcanonical hb hc hbc hredBC
    have hdistinct : PairwiseDistinct (⟨a, ha⟩ : Fin 16) ⟨b, hb⟩ ⟨c, hc⟩ :=
      ⟨Fin.ne_of_lt hab, Fin.ne_of_lt hac, Fin.ne_of_lt hbc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hclause
    rcases hclause with rfl | rfl
    · by_cases hab1 : d ⟨a, ha⟩ ⟨b, hb⟩ = (1 : ThreeColor)
      · apply FiniteColorCNF.satisfies_of_mem_holds (clebschCompletionValuation d)
          (l := Sat.Literal.pos (clebschComplementIndex a b)) (List.Mem.head _)
        exact hAB.mpr hab1
      · by_cases hac1 : d ⟨a, ha⟩ ⟨c, hc⟩ = (1 : ThreeColor)
        · apply FiniteColorCNF.satisfies_of_mem_holds (clebschCompletionValuation d)
            (l := Sat.Literal.pos (clebschComplementIndex a c))
            (List.Mem.tail _ (List.Mem.head _))
          exact hAC.mpr hac1
        · by_cases hbc1 : d ⟨b, hb⟩ ⟨c, hc⟩ = (1 : ThreeColor)
          · apply FiniteColorCNF.satisfies_of_mem_holds (clebschCompletionValuation d)
              (l := Sat.Literal.pos (clebschComplementIndex b c))
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            exact hBC.mpr hbc1
          · exfalso
            apply hd ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hdistinct
            have hab2 := fin3_eq_two_of_ne_zero_ne_one _ hn0AB hab1
            have hac2 := fin3_eq_two_of_ne_zero_ne_one _ hn0AC hac1
            have hbc2 := fin3_eq_two_of_ne_zero_ne_one _ hn0BC hbc1
            exact ⟨hab2.trans hac2.symm, hac2.trans hbc2.symm⟩
    · by_cases hab1 : d ⟨a, ha⟩ ⟨b, hb⟩ = (1 : ThreeColor)
      · by_cases hac1 : d ⟨a, ha⟩ ⟨c, hc⟩ = (1 : ThreeColor)
        · by_cases hbc1 : d ⟨b, hb⟩ ⟨c, hc⟩ = (1 : ThreeColor)
          · exfalso
            exact hd ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hdistinct
              ⟨hab1.trans hac1.symm, hac1.trans hbc1.symm⟩
          · apply FiniteColorCNF.satisfies_of_mem_holds (clebschCompletionValuation d)
              (l := Sat.Literal.neg (clebschComplementIndex b c))
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            change ¬clebschCompletionValuation d (clebschComplementIndex b c)
            exact fun hv => hbc1 (hBC.mp hv)
        · apply FiniteColorCNF.satisfies_of_mem_holds (clebschCompletionValuation d)
            (l := Sat.Literal.neg (clebschComplementIndex a c))
            (List.Mem.tail _ (List.Mem.head _))
          change ¬clebschCompletionValuation d (clebschComplementIndex a c)
          exact fun hv => hac1 (hAC.mp hv)
      · apply FiniteColorCNF.satisfies_of_mem_holds (clebschCompletionValuation d)
          (l := Sat.Literal.neg (clebschComplementIndex a b)) (List.Mem.head _)
        change ¬clebschCompletionValuation d (clebschComplementIndex a b)
        exact fun hv => hab1 (hAB.mp hv)

/-- The checked LRAT proof is now a mathematical exhaustion theorem: every
good completion of the canonical Clebsch zero graph is literally one of the
seventy-two listed Boolean rows. -/
theorem clebschCompletionBits_mem
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d)
    (hcanonical : HasCanonicalClebschZero d) :
    clebschCompletionBits d ∈ clebschDecompositions := by
  by_contra hnot
  have hactualLength : (clebschCompletionBits d).length = 80 := by
    simp [clebschCompletionBits, clebschComplementEdges_length]
  have htri := coloring_satisfies_clebschCompletionTriangles d hd hcanonical
  have hblockers :
      (clebschCompletionValuation d).satisfies_fmla
        (clebschDecompositions.map clebschCompletionBlocker) := by
    constructor
    intro clause hclause
    simp only [List.mem_map] at hclause
    obtain ⟨bits, hbitsMem, rfl⟩ := hclause
    have hbitsLength := clebschDecomposition_lengths bits hbitsMem
    have hne : clebschCompletionBits d ≠ bits := by
      intro heq
      apply hnot
      simpa [heq] using hbitsMem
    change Sat.Valuation.satisfies
      (fun i => (clebschCompletionBits d).getD i false = true)
      (clebschCompletionBlocker bits)
    exact valuation_satisfies_completionBlocker
      (clebschCompletionBits d) bits hactualLength hbitsLength hne
  have hall : (clebschCompletionValuation d).satisfies_fmla
      clebschCompletionFmla := by
    unfold clebschCompletionFmla
    exact CatalogueBaseCNF.satisfies_fmla_append htri hblockers
  exact clebschCompletion_unsat (clebschCompletionValuation d) hall

#print axioms R4333.clebschCompletionValuation_edge
#print axioms R4333.valuation_satisfies_completionBlocker
#print axioms R4333.coloring_satisfies_clebschCompletionTriangles
#print axioms R4333.clebschCompletionBits_mem

end R4333
