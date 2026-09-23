import R4333Lean.ProfileDFromBFreeCompletionCNF
import R4333Lean.ProfileDBlockZeroSupportShadows

/-!
# Strong compact profile-D target with completion and block-zero cuts

This is the native degree-floored profile-D target obtained by combining:

* the compact lower and upper support counters;
* the thirty profile-C-conditional cross-K15 completion clauses;
* the eight profile-B-conditional free-row completion clauses; and
* twelve unconditional blockwise colour-zero hit clauses (one for each of
  four free rows and three critical tail blocks).

The semantic order is acyclic: B justifies the eight free-completion cuts,
C justifies the thirty cross-K15 cuts, and the native D degree floor itself
justifies the twelve block-zero cuts.  Consequently the endpoint below is
deliberately a degree-floored D obstruction, not a raw universal D
obstruction.  No refutation certificate is asserted.
-/

namespace R4333
namespace ProfileDCompactFreeCompletionBlockZeroCNF

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ThresholdDegreeCapsCNF
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDFourRowBoundary ProfileDRowSupportBounds61

set_option maxRecDepth 1000000

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev FourExtension := ProfileDFourRowBoundary.FourExtension
abbrev DegreeFlooredFourExtension :=
  ProfileDRowSupportBounds61.DegreeFlooredFourExtension
abbrev compactCounterSpecs :=
  ProfileDCompactDegreeFlooredCNF.compactCounterSpecs

/-! ## Twelve blockwise colour-zero hit clauses -/

/-- The first total-graph coordinate of a profile-D tail block. -/
def blockTotalStart (block : Fin 3) : Nat :=
  4 + blockStart block

theorem total_tail_block_coordinate (block : Fin 3) (i : Nat)
    (hi : i < blockSize block) :
    (ProfileDFourRowCNF.tailVertex (blockVertex block i)).val =
      blockTotalStart block + i := by
  simp [ProfileDFourRowCNF.tailVertex, blockTotalStart,
    blockVertex_val block hi, Nat.add_assoc]

def blockZeroHitClause (a : FourVertex) (block : Fin 3) : Sat.Clause :=
  (List.range (blockSize block)).map fun i =>
    Sat.Literal.pos (edgeAtom a.val (blockTotalStart block + i) 0)

def blockZeroHitClauses : Sat.Fmla :=
  (List.finRange 4).flatMap fun a =>
    (List.finRange 3).map (blockZeroHitClause a)

theorem blockZeroHitClauses_length : blockZeroHitClauses.length = 12 := by
  simp [blockZeroHitClauses]

theorem exists_zero_in_block {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (a : FourVertex)
    (block : Fin 3) :
    ∃ i, i < blockSize block ∧
      ext.toFourExtension.rows a (blockVertex block i) = 0 := by
  obtain ⟨hzero0, hzero1, hzero2⟩ :=
    ProfileDBlockZeroSupport.every_block_has_zero ext a
  fin_cases block
  · obtain ⟨i, hi⟩ := hzero0
    exact ⟨i.val, i.isLt, hi⟩
  · obtain ⟨i, hi⟩ := hzero1
    exact ⟨i.val, i.isLt, hi⟩
  · obtain ⟨i, hi⟩ := hzero2
    exact ⟨i.val, i.isLt, hi⟩

theorem coloringValuation_satisfies_blockZeroHitClause {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (a : FourVertex)
    (block : Fin 3) :
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext.toFourExtension)).satisfies
        (blockZeroHitClause a block) := by
  obtain ⟨i, hi, hzero⟩ := exists_zero_in_block ext a block
  let source : ProfileDFourRowCNF.TotalVertex :=
    ProfileDFourRowCNF.freeVertex a
  let target : ProfileDFourRowCNF.TotalVertex :=
    ProfileDFourRowCNF.tailVertex (blockVertex block i)
  have hsource : source.val = a.val := rfl
  have htarget : target.val = blockTotalStart block + i :=
    total_tail_block_coordinate block i hi
  apply satisfies_of_mem_holds
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext.toFourExtension))
    (l := Sat.Literal.pos
      (edgeAtom a.val (blockTotalStart block + i) 0))
  · unfold blockZeroHitClause
    apply List.mem_map.mpr
    exact ⟨i, List.mem_range.mpr hi, rfl⟩
  · change coloringValuation
      (ProfileDFourRowCNF.totalColoring ext.toFourExtension)
      (edgeAtom a.val (blockTotalStart block + i) 0)
    have hatom : edgeAtom a.val (blockTotalStart block + i) 0 =
        edgeAtom source target (0 : Fin 4) := by
      simp [hsource, htarget]
    rw [hatom, coloringValuation_edgeAtom]
    change ProfileDFourRowCNF.totalColoring ext.toFourExtension
      (ProfileDFourRowCNF.freeVertex a)
      (ProfileDFourRowCNF.tailVertex (blockVertex block i)) = 0
    rw [ProfileDFromBFreeCompletionCNF.totalColoring_free_tail]
    exact hzero

theorem coloringValuation_satisfies_blockZeroHitClauses {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext.toFourExtension)).satisfies_fmla
        blockZeroHitClauses := by
  constructor
  intro clause hclause
  obtain ⟨a, _ha, hclause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨block, _hblock, rfl⟩ := List.mem_map.mp hclause
  exact coloringValuation_satisfies_blockZeroHitClause ext a block

/-! ## Namespace separation for the edge-only additions -/

private theorem freeRowsHitFirstK15Clauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      ((List.finRange 4).map
        ProfileDFromBFreeCompletionCNF.freeRowHitsFirstK15Clause) := by
  intro clause hclause literal hliteral
  obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hclause
  change literal ∈ (List.finRange 15).map (fun x =>
    Sat.Literal.pos (edgeAtom a.val (4 + x.val) 1)) at hliteral
  obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hliteral
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    reservedX reservedQ (by omega) (by omega)

private theorem freeRowsHitSecondK15Clauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      ((List.finRange 4).map
        ProfileDFromBFreeCompletionCNF.freeRowHitsSecondK15Clause) := by
  intro clause hclause literal hliteral
  obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hclause
  change literal ∈ (List.finRange 15).map (fun x =>
    Sat.Literal.pos (edgeAtom a.val (19 + x.val) 2)) at hliteral
  obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hliteral
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    reservedX reservedQ (by omega) (by omega)

theorem freeRowsHitBothK15Clauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      ProfileDFromBFreeCompletionCNF.freeRowsHitBothK15Clauses := by
  unfold ProfileDFromBFreeCompletionCNF.freeRowsHitBothK15Clauses
  apply formulaOutsideNamespace_append
  · exact freeRowsHitFirstK15Clauses_outside_largerCounterNamespace
      hn reservedX reservedQ
  · exact freeRowsHitSecondK15Clauses_outside_largerCounterNamespace
      hn reservedX reservedQ

theorem blockZeroHitClauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      blockZeroHitClauses := by
  intro clause hclause literal hliteral
  obtain ⟨a, _ha, hclause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨block, _hblock, rfl⟩ := List.mem_map.mp hclause
  change literal ∈ (List.range (blockSize block)).map (fun i =>
    Sat.Literal.pos
      (edgeAtom a.val (blockTotalStart block + i) 0)) at hliteral
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hliteral
  have hi' := List.mem_range.mp hi
  have hright : blockTotalStart block + i < 50 := by
    fin_cases block <;>
      simp [blockTotalStart, blockStart, blockSize] at hi' ⊢ <;> omega
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    reservedX reservedQ (by omega) (by omega)

/-! ## Compact formula and explicit satisfying valuation -/

def compactBaseFmla (kind : Kind) : Sat.Fmla :=
  (ProfileDCompactDegreeFlooredCNF.conditionalCompactBaseFmla kind ++
    ProfileDFromBFreeCompletionCNF.freeRowsHitBothK15Clauses) ++
      blockZeroHitClauses

def fmla (kind : Kind) : Sat.Fmla :=
  manySequentialAtMostFmla (compactBaseFmla kind) compactCounterSpecs

theorem compactCounterSpecs_wellFormed (kind : Kind) :
    ManyCounterWellFormed (compactBaseFmla kind) compactCounterSpecs := by
  let old :=
    ProfileDCompactDegreeFlooredCNF.conditionalCompactCounterSpecs_wellFormed
      kind
  refine ⟨old.tags_nodup, ?_, old.inputs_outside⟩
  intro reserved hreserved
  unfold compactBaseFmla
  apply formulaOutsideNamespace_append
  · apply formulaOutsideNamespace_append
    · exact old.base_outside reserved hreserved
    · have hreserved' : reserved ∈ compactCounterSpecs := hreserved
      simp only [compactCounterSpecs,
        ProfileDCompactDegreeFlooredCNF.compactCounterSpecs,
        List.mem_map] at hreserved'
      obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hreserved'
      exact freeRowsHitBothK15Clauses_outside_largerCounterNamespace
        (n := 61) (by omega)
        (ProfileDCompactDegreeFlooredCNF.compactNamespaceVertex a phase) q
  · have hreserved' : reserved ∈ compactCounterSpecs := hreserved
    simp only [compactCounterSpecs,
      ProfileDCompactDegreeFlooredCNF.compactCounterSpecs,
      List.mem_map] at hreserved'
    obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hreserved'
    exact blockZeroHitClauses_outside_largerCounterNamespace
      (n := 61) (by omega)
      (ProfileDCompactDegreeFlooredCNF.compactNamespaceVertex a phase) q

theorem complementValuation_satisfies_freeRowsHitBothK15Clauses
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (ProfileDCompactDegreeFlooredCNF.complementValuation ext).satisfies_fmla
      ProfileDFromBFreeCompletionCNF.freeRowsHitBothK15Clauses := by
  exact ComplementAtomCNF.complementExtension_satisfies_base
    ProfileDCompactDegreeFlooredCNF.complementNamespaceTag
    ProfileDCompactDegreeFlooredCNF.complementSourceAtom
    ProfileDFromBFreeCompletionCNF.freeRowsHitBothK15Clauses
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
    (freeRowsHitBothK15Clauses_outside_largerCounterNamespace
      (n := 60) (by omega)
      ProfileDCompactDegreeFlooredCNF.complementNamespaceVertex
      ProfileDCompactDegreeFlooredCNF.complementNamespaceColor)
    (ProfileDFromBFreeCompletionCNF.satisfies_freeRowsHitBothK15Clauses
      hB ext)

theorem complementValuation_satisfies_blockZeroHitClauses {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    (ProfileDCompactDegreeFlooredCNF.complementValuation
      ext.toFourExtension).satisfies_fmla blockZeroHitClauses := by
  exact ComplementAtomCNF.complementExtension_satisfies_base
    ProfileDCompactDegreeFlooredCNF.complementNamespaceTag
    ProfileDCompactDegreeFlooredCNF.complementSourceAtom
    blockZeroHitClauses
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext.toFourExtension))
    (blockZeroHitClauses_outside_largerCounterNamespace
      (n := 60) (by omega)
      ProfileDCompactDegreeFlooredCNF.complementNamespaceVertex
      ProfileDCompactDegreeFlooredCNF.complementNamespaceColor)
    (coloringValuation_satisfies_blockZeroHitClauses ext)

theorem degreeFlooredFourExtension_satisfies_fmla
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : DegreeFlooredFourExtension kind) :
    (iteratedSequentialExtension compactCounterSpecs
      (ProfileDCompactDegreeFlooredCNF.complementValuation
        ext.toFourExtension)).satisfies_fmla (fmla kind) := by
  apply iteratedExtension_satisfies_manySequentialAtMostFmla
    (compactBaseFmla kind) compactCounterSpecs
    (ProfileDCompactDegreeFlooredCNF.complementValuation
      ext.toFourExtension)
    (compactCounterSpecs_wellFormed kind)
  · constructor
    intro clause hclause
    rcases List.mem_append.mp hclause with hconditionalFree | hzero
    · rcases List.mem_append.mp hconditionalFree with hconditional | hfree
      · rcases List.mem_append.mp hconditional with hcompact | hcompletion
        · rcases List.mem_append.mp hcompact with hraw | hdefinitions
          · exact
              (ProfileDCompactDegreeFlooredCNF.complementValuation_satisfies_rawFmla
                ext.toFourExtension).prop clause hraw
          · exact
              (ProfileDCompactDegreeFlooredCNF.complementValuation_satisfies_definitions
                ext.toFourExtension).prop clause hdefinitions
        · exact
            (ProfileDCompactDegreeFlooredCNF.complementValuation_satisfies_bidirectionalCompletionClauses
              hC ext.toFourExtension).prop clause hcompletion
      · exact
          (complementValuation_satisfies_freeRowsHitBothK15Clauses
            hB ext.toFourExtension).prop clause hfree
    · exact (complementValuation_satisfies_blockZeroHitClauses ext).prop
        clause hzero
  · exact ProfileDCompactDegreeFlooredCNF.allCaps_of_degreeFlooredFourExtension
      ext

/-! ## Exact count and degree-floored endpoints -/

theorem compactBaseFmla_length (kind : Kind) :
    (compactBaseFmla kind).length = 88833 := by
  simp [compactBaseFmla,
    ProfileDCompactDegreeFlooredCNF.conditionalCompactBaseFmla_length,
    ProfileDFromBFreeCompletionCNF.freeRowsHitBothK15Clauses_length,
    blockZeroHitClauses_length]

theorem fmla_length (kind : Kind) : (fmla kind).length = 165937 := by
  rw [fmla, manySequentialAtMostFmla_length, compactBaseFmla_length,
    ProfileDCompactDegreeFlooredCNF.compactCounterClauseContribution]

theorem noDegreeFlooredFourExtension_of_B_C_obstruction_lrat
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (kind : Kind) (hunsat : (fmla kind).proof []) :
    ¬Nonempty (DegreeFlooredFourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat _
    (degreeFlooredFourExtension_satisfies_fmla hB hC ext)

structure RepresentativeLRATRefutations : Prop where
  uuu : (fmla .uuu).proof []
  uut : (fmla .uut).proof []
  utu : (fmla .utu).proof []
  utt : (fmla .utt).proof []
  ttu : (fmla .ttu).proof []
  ttt : (fmla .ttt).proof []

theorem RepresentativeLRATRefutations.obstructions
    (h : RepresentativeLRATRefutations)
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction) :
    SwapRepresentativeDegreeFlooredObstructions where
  uuu := noDegreeFlooredFourExtension_of_B_C_obstruction_lrat
    hB hC .uuu h.uuu
  uut := noDegreeFlooredFourExtension_of_B_C_obstruction_lrat
    hB hC .uut h.uut
  utu := noDegreeFlooredFourExtension_of_B_C_obstruction_lrat
    hB hC .utu h.utu
  utt := noDegreeFlooredFourExtension_of_B_C_obstruction_lrat
    hB hC .utt h.utt
  ttu := noDegreeFlooredFourExtension_of_B_C_obstruction_lrat
    hB hC .ttu h.ttu
  ttt := noDegreeFlooredFourExtension_of_B_C_obstruction_lrat
    hB hC .ttt h.ttt

theorem no_profileD_star_of_B_C_obstruction_lrat
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (h : RepresentativeLRATRefutations) :
    ¬Nonempty (SingleRootStarCNF.CanonicalStarWitness ProfileD) :=
  no_profileD_star_of_swapRepresentativeDegreeFlooredObstructions
    (h.obstructions hB hC)

#print axioms R4333.ProfileDCompactFreeCompletionBlockZeroCNF.exists_zero_in_block
#print axioms R4333.ProfileDCompactFreeCompletionBlockZeroCNF.compactCounterSpecs_wellFormed
#print axioms R4333.ProfileDCompactFreeCompletionBlockZeroCNF.degreeFlooredFourExtension_satisfies_fmla
#print axioms R4333.ProfileDCompactFreeCompletionBlockZeroCNF.fmla_length
#print axioms R4333.ProfileDCompactFreeCompletionBlockZeroCNF.no_profileD_star_of_B_C_obstruction_lrat

end ProfileDCompactFreeCompletionBlockZeroCNF
end R4333
