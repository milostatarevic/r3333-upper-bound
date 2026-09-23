import R4333Lean.ProfileDToBFreeCompletionTransfer
import R4333Lean.ProfileDCompactDegreeFlooredCNF

/-!
# B-conditional free-to-K15 completion cuts for profile D

After profile B is obstructed, each of D's four free vertices must use the
omitted colour on each of D's two K15 blocks.  Otherwise it completes that
K15 to a K16 and the exact transfer in
`ProfileDToBFreeCompletionTransfer` produces a forbidden B three-row object.

This file appends the resulting eight length-fifteen clauses to the existing
raw bidirectional D formula.  Thus its soundness premises are acyclic in the
order `B`, then `C`, then `D`: B justifies these eight clauses and C justifies
the thirty cross-K15 clauses.  No refutation certificate is supplied.
-/

namespace R4333
namespace ProfileDFromBFreeCompletionCNF

open FiniteColorCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary

set_option maxRecDepth 1000000

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev FourExtension := ProfileDFourRowBoundary.FourExtension

/-- Free row `a` uses colour one on the first K15 (`total` positions 4--18). -/
def freeRowHitsFirstK15Clause (a : FourVertex) : Sat.Clause :=
  (List.finRange 15).map fun x ↦
    Sat.Literal.pos (edgeAtom a.val (4 + x.val) 1)

/-- Free row `a` uses colour two on the second K15 (`total` positions 19--33). -/
def freeRowHitsSecondK15Clause (a : FourVertex) : Sat.Clause :=
  (List.finRange 15).map fun x ↦
    Sat.Literal.pos (edgeAtom a.val (19 + x.val) 2)

def freeRowsHitBothK15Clauses : Sat.Fmla :=
  (List.finRange 4).map freeRowHitsFirstK15Clause ++
    (List.finRange 4).map freeRowHitsSecondK15Clause

theorem freeRowHitsFirstK15Clause_length (a : FourVertex) :
    (freeRowHitsFirstK15Clause a).length = 15 := by
  simp [freeRowHitsFirstK15Clause]

theorem freeRowHitsSecondK15Clause_length (a : FourVertex) :
    (freeRowHitsSecondK15Clause a).length = 15 := by
  simp [freeRowHitsSecondK15Clause]

theorem freeRowsHitBothK15Clauses_length :
    freeRowsHitBothK15Clauses.length = 8 := by
  simp [freeRowsHitBothK15Clauses]

/-- The 87,341-clause raw C-conditional D formula plus all eight
B-conditional free-completion blockers. -/
def fmla (kind : Kind) : Sat.Fmla :=
  ProfileDCompactDegreeFlooredCNF.rawBidirectionalConditionalFmla kind ++
    freeRowsHitBothK15Clauses

theorem fmla_length (kind : Kind) : (fmla kind).length = 87349 := by
  simp [fmla,
    ProfileDCompactDegreeFlooredCNF.rawBidirectionalConditionalFmla_length,
    freeRowsHitBothK15Clauses_length]

@[simp] theorem totalColoring_free_tail {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (x : TailVertex) :
    ProfileDFourRowCNF.totalColoring ext
        (ProfileDFourRowCNF.freeVertex a)
        (ProfileDFourRowCNF.tailVertex x) = ext.rows a x := by
  simp [ProfileDFourRowCNF.totalColoring, pullbackColoring]

theorem satisfies_freeRowHitsFirstK15Clause
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : Kind} (ext : FourExtension kind) (a : FourVertex) :
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext)).satisfies
      (freeRowHitsFirstK15Clause a) := by
  obtain ⟨x, hx⟩ :=
    ProfileDToBFreeCompletionTransfer.every_free_row_hits_firstK15_of_B_obstruction
      hB ext a
  let core : TailVertex := blockVertex 0 x.val
  have hcore : core.val = x.val := by
    simp [core, blockVertex_val 0 x.isLt, blockStart]
  apply satisfies_of_mem_holds
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
    (l := Sat.Literal.pos (edgeAtom a.val (4 + x.val) 1))
  · unfold freeRowHitsFirstK15Clause
    exact List.mem_map.mpr ⟨x, by simp, rfl⟩
  · change coloringValuation (ProfileDFourRowCNF.totalColoring ext)
      (edgeAtom a.val (4 + x.val) 1)
    have hatom : edgeAtom a.val (4 + x.val) 1 =
        edgeAtom (ProfileDFourRowCNF.freeVertex a)
          (ProfileDFourRowCNF.tailVertex core) (1 : Fin 4) := by
      simp [ProfileDFourRowCNF.freeVertex,
        ProfileDFourRowCNF.tailVertex, hcore]
    rw [hatom, coloringValuation_edgeAtom]
    rw [totalColoring_free_tail]
    simpa [core] using hx

theorem satisfies_freeRowHitsSecondK15Clause
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : Kind} (ext : FourExtension kind) (a : FourVertex) :
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext)).satisfies
      (freeRowHitsSecondK15Clause a) := by
  obtain ⟨x, hx⟩ :=
    ProfileDToBFreeCompletionTransfer.every_free_row_hits_secondK15_of_B_obstruction
      hB ext a
  let core : TailVertex := blockVertex 1 x.val
  have hcore : core.val = 15 + x.val := by
    simp [core, blockVertex_val 1 x.isLt, blockStart]
  have hright : (ProfileDFourRowCNF.tailVertex core).val = 19 + x.val := by
    simp [ProfileDFourRowCNF.tailVertex, hcore]
    omega
  apply satisfies_of_mem_holds
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
    (l := Sat.Literal.pos (edgeAtom a.val (19 + x.val) 2))
  · unfold freeRowHitsSecondK15Clause
    exact List.mem_map.mpr ⟨x, by simp, rfl⟩
  · change coloringValuation (ProfileDFourRowCNF.totalColoring ext)
      (edgeAtom a.val (19 + x.val) 2)
    have hatom : edgeAtom a.val (19 + x.val) 2 =
        edgeAtom (ProfileDFourRowCNF.freeVertex a)
          (ProfileDFourRowCNF.tailVertex core) (2 : Fin 4) := by
      simp [ProfileDFourRowCNF.freeVertex, hright]
    rw [hatom, coloringValuation_edgeAtom]
    rw [totalColoring_free_tail]
    simpa [core] using hx

theorem satisfies_freeRowsHitBothK15Clauses
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext)).satisfies_fmla
      freeRowsHitBothK15Clauses := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hfirst | hsecond
  · obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hfirst
    exact satisfies_freeRowHitsFirstK15Clause hB ext a
  · obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hsecond
    exact satisfies_freeRowHitsSecondK15Clause hB ext a

/-- Every D four-row object satisfies all 38 conditional clauses in the
acyclic B-then-C proof order. -/
theorem fourExtension_satisfies_fmla
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext)).satisfies_fmla
      (fmla kind) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hbase | hfree
  · exact
      (ProfileDCompactDegreeFlooredCNF.fourExtension_satisfies_rawBidirectionalConditionalFmla
        hC ext).prop clause hbase
  · exact (satisfies_freeRowsHitBothK15Clauses hB ext).prop clause hfree

theorem noFourExtension_of_B_C_obstruction_lrat
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (kind : Kind) (hunsat : (fmla kind).proof []) :
    ¬Nonempty (FourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
    (fourExtension_satisfies_fmla hB hC ext)

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
    ProfileDFourRowKindSymmetry.SwapRepresentativeObstructions where
  uuu := noFourExtension_of_B_C_obstruction_lrat hB hC .uuu h.uuu
  uut := noFourExtension_of_B_C_obstruction_lrat hB hC .uut h.uut
  utu := noFourExtension_of_B_C_obstruction_lrat hB hC .utu h.utu
  utt := noFourExtension_of_B_C_obstruction_lrat hB hC .utt h.utt
  ttu := noFourExtension_of_B_C_obstruction_lrat hB hC .ttu h.ttu
  ttt := noFourExtension_of_B_C_obstruction_lrat hB hC .ttt h.ttt

theorem RepresentativeLRATRefutations.universalFourRowObstruction
    (h : RepresentativeLRATRefutations)
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction) :
    ProfileDFourRowBoundary.UniversalFourRowObstruction :=
  (h.obstructions hB hC).universalFourRowObstruction

#print axioms R4333.ProfileDFromBFreeCompletionCNF.fourExtension_satisfies_fmla
#print axioms R4333.ProfileDFromBFreeCompletionCNF.noFourExtension_of_B_C_obstruction_lrat
#print axioms R4333.ProfileDFromBFreeCompletionCNF.RepresentativeLRATRefutations.universalFourRowObstruction

end ProfileDFromBFreeCompletionCNF
end R4333
