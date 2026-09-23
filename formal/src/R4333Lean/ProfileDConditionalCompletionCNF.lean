import R4333Lean.ProfileDToCCompletionTransfer
import R4333Lean.ProfileDFourRowCNF

/-!
# Profile-C-conditional completion clauses for profile D

Once every profile-C four-row extension is obstructed, the exact D-to-C
vertex transfer forces every vertex of D's first K15 to have at least one
colour-two edge into D's second K15.  In the authoritative profile-D
`Fin 50` order this gives exactly fifteen positive clauses, each of length
fifteen.

This file appends those clauses to the ordinary profile-D formula, proves
their semantic soundness under a universal profile-C obstruction, and
packages the six genuine D kind representatives.  It supplies no
refutation certificates.
-/

namespace R4333
namespace ProfileDConditionalCompletionCNF

open FiniteColorCNF
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary

set_option maxRecDepth 1000000

/-- For one vertex of the first K15, some edge into the second K15 has the
second block's omitted host colour, namely colour two.  The two blocks occupy
total-coordinate intervals `4..18` and `19..33`. -/
def firstVertexHitsSecondK15Clause (source : Fin 15) : Sat.Clause :=
  (List.finRange 15).map fun target =>
    Sat.Literal.pos (FiniteColorCNF.edgeAtom
      (4 + source.val) (19 + target.val) 2)

/-- Exactly one completion-blocking clause for each first-K15 vertex. -/
def firstVerticesHitSecondK15Clauses : Sat.Fmla :=
  (List.finRange 15).map firstVertexHitsSecondK15Clause

theorem firstVertexHitsSecondK15Clause_length (source : Fin 15) :
    (firstVertexHitsSecondK15Clause source).length = 15 := by
  simp [firstVertexHitsSecondK15Clause]

theorem firstVerticesHitSecondK15Clauses_length :
    firstVerticesHitSecondK15Clauses.length = 15 := by
  simp [firstVerticesHitSecondK15Clauses]

theorem firstVerticesHitSecondK15Clauses_clause_length
    {clause : Sat.Clause}
    (hclause : clause ∈ firstVerticesHitSecondK15Clauses) :
    clause.length = 15 := by
  simp only [firstVerticesHitSecondK15Clauses, List.mem_map] at hclause
  obtain ⟨source, _, rfl⟩ := hclause
  exact firstVertexHitsSecondK15Clause_length source

/-- The C-conditional strengthened profile-D formula. -/
def fmla (kind : Kind) : Sat.Fmla :=
  ProfileDFourRowCNF.fmla kind ++ firstVerticesHitSecondK15Clauses

private theorem firstVertex_has_blocking_edge
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) (source : Fin 15) :
    ∃ target : Fin 15,
      ext.tail.coloring
          (blockVertex 0 source.val) (blockVertex 1 target.val) = 2 := by
  have hnotCompletion :
      ¬ProfileDToCCompletionTransfer.CompletesSecondK15 ext source := by
    intro hcompletion
    exact hC (ProfileDToCCompletionTransfer.toCKind kind)
      ⟨ProfileDToCCompletionTransfer.transferWith
        ext source hcompletion⟩
  by_contra hnone
  apply hnotCompletion
  apply (ProfileDToCCompletionTransfer.completesSecondK15_iff_avoids
    ext source).2
  intro target hcolour
  apply hnone
  exact ⟨target, hcolour⟩

theorem satisfies_firstVertexHitsSecondK15Clause
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) (source : Fin 15) :
    (FiniteColorCNF.coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)).satisfies
        (firstVertexHitsSecondK15Clause source) := by
  obtain ⟨target, htarget⟩ :=
    firstVertex_has_blocking_edge hC ext source
  let sourceTail : ProfileDRowExtension.TailVertex :=
    blockVertex 0 source.val
  let targetTail : ProfileDRowExtension.TailVertex :=
    blockVertex 1 target.val
  let left : ProfileDFourRowCNF.TotalVertex :=
    ProfileDFourRowCNF.tailVertex sourceTail
  let right : ProfileDFourRowCNF.TotalVertex :=
    ProfileDFourRowCNF.tailVertex targetTail
  let two : Fin 4 := 2
  have hsourceTail : sourceTail.val = source.val := by
    simp [sourceTail, blockVertex_val 0 source.isLt,
      ProfileDTripleJoinReduction.blockStart]
  have htargetTail : targetTail.val = 15 + target.val := by
    simp [targetTail, blockVertex_val 1 target.isLt,
      ProfileDTripleJoinReduction.blockStart]
  have hleft : left.val = 4 + source.val := by
    simp [left, ProfileDFourRowCNF.tailVertex, hsourceTail]
  have hright : right.val = 19 + target.val := by
    simp [right, ProfileDFourRowCNF.tailVertex, htargetTail]
    omega
  apply FiniteColorCNF.satisfies_of_mem_holds
    (FiniteColorCNF.coloringValuation
      (ProfileDFourRowCNF.totalColoring ext))
    (l := Sat.Literal.pos (FiniteColorCNF.edgeAtom
      (4 + source.val) (19 + target.val) two.val))
  · unfold firstVertexHitsSecondK15Clause
    apply List.mem_map.mpr
    exact ⟨target, by simp, rfl⟩
  · change FiniteColorCNF.coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)
      (FiniteColorCNF.edgeAtom
        (4 + source.val) (19 + target.val) two.val)
    have hatom :
        FiniteColorCNF.edgeAtom
            (4 + source.val) (19 + target.val) two.val =
          FiniteColorCNF.edgeAtom left right two := by
      simp [hleft, hright]
    rw [hatom, FiniteColorCNF.coloringValuation_edgeAtom]
    change ProfileDFourRowCNF.totalColoring ext
        (ProfileDFourRowCNF.tailVertex sourceTail)
        (ProfileDFourRowCNF.tailVertex targetTail) = two
    rw [ProfileDFourRowCNF.totalColoring_tail_tail]
    simpa [sourceTail, targetTail, two] using htarget

theorem satisfies_firstVerticesHitSecondK15Clauses
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (FiniteColorCNF.coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)).satisfies_fmla
        firstVerticesHitSecondK15Clauses := by
  constructor
  intro clause hclause
  simp only [firstVerticesHitSecondK15Clauses, List.mem_map] at hclause
  obtain ⟨source, _, rfl⟩ := hclause
  exact satisfies_firstVertexHitsSecondK15Clause hC ext source

/-- Every D four-row object satisfies the strengthened formula once the C
branch has been universally obstructed. -/
theorem fourExtension_satisfies_fmla
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (FiniteColorCNF.coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)).satisfies_fmla
        (fmla kind) := by
  constructor
  intro clause hclause
  simp only [fmla, List.mem_append] at hclause
  rcases hclause with hbase | hcompletion
  · exact (ProfileDFourRowCNF.fourExtension_satisfies_fmla ext).prop
      clause hbase
  · exact (satisfies_firstVerticesHitSecondK15Clauses hC ext).prop
      clause hcompletion

theorem noFourExtension_of_C_obstruction_lrat
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (kind : Kind) (hunsat : (fmla kind).proof Sat.Clause.nil) :
    ¬Nonempty (FourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat
    (FiniteColorCNF.coloringValuation
      (ProfileDFourRowCNF.totalColoring ext))
    (fourExtension_satisfies_fmla hC ext)

/-- Six checked strengthened-D refutations, one for each orbit under the
equal-K15 block swap. -/
structure RepresentativeLRATRefutations : Prop where
  uuu : (fmla .uuu).proof Sat.Clause.nil
  uut : (fmla .uut).proof Sat.Clause.nil
  utu : (fmla .utu).proof Sat.Clause.nil
  utt : (fmla .utt).proof Sat.Clause.nil
  ttu : (fmla .ttu).proof Sat.Clause.nil
  ttt : (fmla .ttt).proof Sat.Clause.nil

theorem RepresentativeLRATRefutations.obstructions
    (h : RepresentativeLRATRefutations)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction) :
    ProfileDFourRowKindSymmetry.SwapRepresentativeObstructions where
  uuu := noFourExtension_of_C_obstruction_lrat hC .uuu h.uuu
  uut := noFourExtension_of_C_obstruction_lrat hC .uut h.uut
  utu := noFourExtension_of_C_obstruction_lrat hC .utu h.utu
  utt := noFourExtension_of_C_obstruction_lrat hC .utt h.utt
  ttu := noFourExtension_of_C_obstruction_lrat hC .ttu h.ttu
  ttt := noFourExtension_of_C_obstruction_lrat hC .ttt h.ttt

/-- The six representatives, interpreted under the C obstruction, cover all
eight D kinds by the equal-K15 symmetry. -/
theorem RepresentativeLRATRefutations.universalFourRowObstruction
    (h : RepresentativeLRATRefutations)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction) :
    ProfileDFourRowBoundary.UniversalFourRowObstruction :=
  (h.obstructions hC).universalFourRowObstruction

#print axioms R4333.ProfileDConditionalCompletionCNF.firstVertex_has_blocking_edge
#print axioms R4333.ProfileDConditionalCompletionCNF.fourExtension_satisfies_fmla
#print axioms R4333.ProfileDConditionalCompletionCNF.noFourExtension_of_C_obstruction_lrat
#print axioms R4333.ProfileDConditionalCompletionCNF.RepresentativeLRATRefutations.obstructions
#print axioms R4333.ProfileDConditionalCompletionCNF.RepresentativeLRATRefutations.universalFourRowObstruction

end ProfileDConditionalCompletionCNF
end R4333
