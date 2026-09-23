import PricingG.UUTD10CatalogEntry
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitCertificateUUU2P15

/-!
# Lift the block-two catalogue orbit actions to exact branches

The stored orbit witnesses act on the free five-cycle and on the two ordered
colour-two supports.  This module proves that those local actions are induced
by actual template automorphisms of the two foreign `K15` blocks and transports
an exact catalogue branch to its stored representative row.
-/

namespace R4333
namespace UUTD10OrbitTransport

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixTransport61
open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogSemanticCompleteness61
open ProfileDUUUDegreeTenCatalogLeafBridgeUUU2P15
open ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
open UUTD10CatalogEntry
open ProfileDUUUDegreeTenEndToEndSemanticUUU0P2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition

abbrev MatrixFiveVertex :=
  ProfileDHighOwnFiveRowSplit61.FiveVertex

/-! ## Relabeling the retained free five-cycle -/

theorem freeAction_insideCanonical
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uut 2 SelectedPosition
      (coordinatesFor first second) matrix)
    (action : Fin 10) (left right : MatrixFiveVertex)
    (hne : left ≠ right) :
    exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
        (freeActionEquiv action left) (freeActionEquiv action right) =
      decodeRemainingColor 2 (!canonicalCycleWord.coloring left right) := by
  rw [exact.branch.insideCanonical _ _
    ((freeActionEquiv action).injective.ne hne)]
  congr 2
  change canonicalCycleWord.coloring (freeAction action left)
      (freeAction action right) = canonicalCycleWord.coloring left right
  exact freeAction_preserves_canonicalCycle action left right hne

theorem freeMatrixPerm_coordinates_covariant
    (first second : SupportRepresentative) (action : Fin 10) (i : Fin 15) :
    totalFreeVertexPerm (freeActionEquiv action)
        ((coordinatesFor first second).vertex i) =
      (coordinatesFor first second).vertex (freeMatrixPerm action i) := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero,
        totalFreeVertexPerm_free]
      change freeVertex (freeActionEquiv action position) =
        (coordinatesFor first second).vertex
          (matrixBlockPerm (freeActionEquiv action) (Equiv.refl _)
            (Equiv.refl _) (blockVertex 0 position))
      rw [matrixBlockPerm_blockZero,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero]
    · rw [threeFiveEquiv_blockOne,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne,
        totalFreeVertexPerm_tail]
      change tailVertex
          (ProfileDTripleJoinReduction.blockVertex 0
            ((coordinatesFor first second).first.embedding position).val) =
        (coordinatesFor first second).vertex
          (matrixBlockPerm (freeActionEquiv action) (Equiv.refl _)
            (Equiv.refl _) (blockVertex 1 position))
      rw [matrixBlockPerm_blockOne,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne]
      rfl
  · rw [threeFiveEquiv_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo,
      totalFreeVertexPerm_tail]
    change tailVertex
        (ProfileDTripleJoinReduction.blockVertex 1
          ((coordinatesFor first second).second.embedding position).val) =
      (coordinatesFor first second).vertex
        (matrixBlockPerm (freeActionEquiv action) (Equiv.refl _)
          (Equiv.refl _) (blockVertex 2 position))
    rw [matrixBlockPerm_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo]
    rfl

noncomputable def freeRelabeledBlockTwoCatalogMatrix
    (first second : SupportRepresentative) (row : Fin 600)
    (action : Fin 10) : EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring (blockTwoCatalogMatrix first second row)
    (freeMatrixPerm action)

noncomputable def relabelCatalogExactByFreeAction
    (first second : SupportRepresentative) (row : Fin 600)
    (exact : ExactDegreeTenMatrixBranch .uut 2 SelectedPosition
      (coordinatesFor first second)
      (blockTwoCatalogMatrix first second row))
    (action : Fin 10) :
    ExactDegreeTenMatrixBranch .uut 2 SelectedPosition
      (coordinatesFor first second)
      (freeRelabeledBlockTwoCatalogMatrix first second row action) :=
  transportExactDegreeTenMatrixBranchByFreePerm exact (freeActionEquiv action)
    (freeAction_insideCanonical first second exact action)
    (freeMatrixPerm action)
    (freeMatrixPerm_coordinates_covariant first second action)
    (matrixBlockPerm_preserves_cross_group _ _ _)
    (by intro left right _; rfl)

/-! ## The common strong stabilizer of all three q=2 representatives -/

theorem q2SupportAction_bijective
    (supportRepresentative : SupportRepresentative) (action : Fin 10) :
    Function.Bijective (q2SupportAction supportRepresentative action) := by
  cases supportRepresentative <;> fin_cases action <;> decide

noncomputable def q2SupportActionEquiv
    (supportRepresentative : SupportRepresentative) (action : Fin 10) :
    Equiv.Perm MatrixFiveVertex :=
  Equiv.ofBijective (q2SupportAction supportRepresentative action)
    (q2SupportAction_bijective supportRepresentative action)

/-- The orbit tables use ten local action slots.  For the two supports with
order-two induced stabilizer, the slots alternate between the identity and
the indicated strong vertex automorphism; support four uses all ten. -/
def q2VertexActionIndex :
    SupportRepresentative → Fin 10 → Fin 10
  | .s0 => ![0, 8, 0, 8, 0, 8, 0, 8, 0, 8]
  | .s1 => ![0, 5, 0, 5, 0, 5, 0, 5, 0, 5]
  | .s4 => fun action => action

theorem q2Stabilizer_canonicalEmbedding
    (supportRepresentative : SupportRepresentative) (action : Fin 10)
    (position : MatrixFiveVertex) :
    u15StabilizerEquiv .support7
        (q2VertexActionIndex supportRepresentative action)
        ((support supportRepresentative).embedding position) =
      (support supportRepresentative).embedding
        (q2SupportActionEquiv supportRepresentative action position) := by
  cases supportRepresentative <;> fin_cases action <;> fin_cases position <;>
    decide

theorem q2Stabilizer_positions
    (supportRepresentative : SupportRepresentative) (action : Fin 10)
    (position : Fin 15) :
    position ∈ (support supportRepresentative).positions ↔
      u15StabilizerEquiv .support7
          (q2VertexActionIndex supportRepresentative action) position ∈
        (support supportRepresentative).positions := by
  cases supportRepresentative <;> fin_cases action <;> fin_cases position <;>
    decide

noncomputable def q2TailStabilizerPerm
    (first second : SupportRepresentative)
    (firstAction secondAction : Fin 10) :
    Equiv.Perm ProfileDRowExtension.TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr
        (u15StabilizerEquiv .support7
          (q2VertexActionIndex first firstAction))
        (u15StabilizerEquiv .support7
          (q2VertexActionIndex second secondAction)))
      (Equiv.refl (Fin 16))).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

@[simp] theorem q2TailStabilizerPerm_blockZero
    (first second : SupportRepresentative)
    (firstAction secondAction : Fin 10) (position : Fin 15) :
    q2TailStabilizerPerm first second firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 0 position.val) =
      ProfileDTripleJoinReduction.blockVertex 0
        (u15StabilizerEquiv .support7
          (q2VertexActionIndex first firstAction) position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp only [q2TailStabilizerPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero _

@[simp] theorem q2TailStabilizerPerm_blockOne
    (first second : SupportRepresentative)
    (firstAction secondAction : Fin 10) (position : Fin 15) :
    q2TailStabilizerPerm first second firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 1 position.val) =
      ProfileDTripleJoinReduction.blockVertex 1
        (u15StabilizerEquiv .support7
          (q2VertexActionIndex second secondAction) position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp only [q2TailStabilizerPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne _

@[simp] theorem q2TailStabilizerPerm_blockTwo
    (first second : SupportRepresentative)
    (firstAction secondAction : Fin 10) (position : Fin 16) :
    q2TailStabilizerPerm first second firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 2 position.val) =
      ProfileDTripleJoinReduction.blockVertex 2 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp [q2TailStabilizerPerm]

theorem q2TailStabilizer_templateCanonical
    (tail : ProfileDTripleJoinReduction.Witness .uut)
    (first second : SupportRepresentative)
    (firstAction secondAction : Fin 10) :
    ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      tail.coloring
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex target left))
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex target right)) =
        SingleRootStarCNF.canonicalPalette (Fin.succ target)
          (SingleRootStarCNF.templateColor (blockSize target)
            (Kind.twisted .uut target) left right) := by
  intro target left right hleft hright hlr
  fin_cases target
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex 0 left))
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex 0 right)) =
        SingleRootStarCNF.canonicalPalette 1
          (SingleRootStarCNF.templateColor 15 false left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 0 left =
        ProfileDTripleJoinReduction.blockVertex 0 leftFin.val by rfl,
      q2TailStabilizerPerm_blockZero,
      show ProfileDTripleJoinReduction.blockVertex 0 right =
        ProfileDTripleJoinReduction.blockVertex 0 rightFin.val by rfl,
      q2TailStabilizerPerm_blockZero]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 0 (by decide)
          (u15StabilizerEquiv .support7
            (q2VertexActionIndex first firstAction) leftFin)
          (u15StabilizerEquiv .support7
            (q2VertexActionIndex first firstAction) rightFin)
          ((u15StabilizerEquiv .support7
            (q2VertexActionIndex first firstAction)).injective.ne hne)
    have htwisted : Kind.uut.twisted (0 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 0
            (u15StabilizerEquiv .support7
              (q2VertexActionIndex first firstAction) leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 0
            (u15StabilizerEquiv .support7
              (q2VertexActionIndex first firstAction) rightFin).val) =
          SingleRootStarCNF.canonicalPalette 1
            (k15Template false
              (u15StabilizerEquiv .support7
                (q2VertexActionIndex first firstAction) leftFin)
              (u15StabilizerEquiv .support7
                (q2VertexActionIndex first firstAction) rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 1
            (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 1)
          (u15StabilizerEquiv_preserves .support7
            (q2VertexActionIndex first firstAction)
            leftFin rightFin hne)
      _ = _ := by
        simp [SingleRootStarCNF.templateColor, SingleRootStarCNF.fin15,
          leftFin, rightFin, Nat.mod_eq_of_lt hleft,
          Nat.mod_eq_of_lt hright]
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex 1 left))
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex 1 right)) =
        SingleRootStarCNF.canonicalPalette 2
          (SingleRootStarCNF.templateColor 15 false left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 1 left =
        ProfileDTripleJoinReduction.blockVertex 1 leftFin.val by rfl,
      q2TailStabilizerPerm_blockOne,
      show ProfileDTripleJoinReduction.blockVertex 1 right =
        ProfileDTripleJoinReduction.blockVertex 1 rightFin.val by rfl,
      q2TailStabilizerPerm_blockOne]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 1 (by decide)
          (u15StabilizerEquiv .support7
            (q2VertexActionIndex second secondAction) leftFin)
          (u15StabilizerEquiv .support7
            (q2VertexActionIndex second secondAction) rightFin)
          ((u15StabilizerEquiv .support7
            (q2VertexActionIndex second secondAction)).injective.ne hne)
    have htwisted : Kind.uut.twisted (1 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1
            (u15StabilizerEquiv .support7
              (q2VertexActionIndex second secondAction) leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 1
            (u15StabilizerEquiv .support7
              (q2VertexActionIndex second secondAction) rightFin).val) =
          SingleRootStarCNF.canonicalPalette 2
            (k15Template false
              (u15StabilizerEquiv .support7
                (q2VertexActionIndex second secondAction) leftFin)
              (u15StabilizerEquiv .support7
                (q2VertexActionIndex second secondAction) rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 2
            (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 2)
          (u15StabilizerEquiv_preserves .support7
            (q2VertexActionIndex second secondAction)
            leftFin rightFin hne)
      _ = _ := by
        simp [SingleRootStarCNF.templateColor, SingleRootStarCNF.fin15,
          leftFin, rightFin, Nat.mod_eq_of_lt hleft,
          Nat.mod_eq_of_lt hright]
  · change left < 16 at hleft
    change right < 16 at hright
    change
      tail.coloring
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex 2 left))
          (q2TailStabilizerPerm first second firstAction secondAction
            (ProfileDTripleJoinReduction.blockVertex 2 right)) =
        SingleRootStarCNF.canonicalPalette 3
          (SingleRootStarCNF.templateColor 16 true left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 2 left =
        ProfileDTripleJoinReduction.blockVertex 2 leftFin.val by rfl,
      q2TailStabilizerPerm_blockTwo,
      show ProfileDTripleJoinReduction.blockVertex 2 right =
        ProfileDTripleJoinReduction.blockVertex 2 rightFin.val by rfl,
      q2TailStabilizerPerm_blockTwo]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        tail 2 (by decide) leftFin rightFin hne
    have htwisted : Kind.uut.twisted (2 : Fin 3) = true := by rfl
    rw [htwisted] at hedge
    simpa [SingleRootStarCNF.templateColor, SingleRootStarCNF.fin16,
      leftFin, rightFin, Nat.mod_eq_of_lt hleft,
      Nat.mod_eq_of_lt hright] using hedge

noncomputable def q2TailMatrixPerm
    (first second : SupportRepresentative)
    (firstAction secondAction : Fin 10) : Equiv.Perm (Fin 15) :=
  matrixBlockPerm (Equiv.refl _)
    (q2SupportActionEquiv first firstAction)
    (q2SupportActionEquiv second secondAction)

theorem q2TailMatrixPerm_coordinates_covariant
    (first second : SupportRepresentative)
    (firstAction secondAction : Fin 10) (i : Fin 15) :
    totalVertexPerm
        (q2TailStabilizerPerm first second firstAction secondAction)
        ((coordinatesFor first second).vertex i) =
      (coordinatesFor first second).vertex
        (q2TailMatrixPerm first second firstAction secondAction i) := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero,
        totalVertexPerm_free]
      change freeVertex position =
        (coordinatesFor first second).vertex
          (matrixBlockPerm (Equiv.refl _)
            (q2SupportActionEquiv first firstAction)
            (q2SupportActionEquiv second secondAction)
            (blockVertex 0 position))
      rw [matrixBlockPerm_blockZero,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero]
      rfl
    · rw [threeFiveEquiv_blockOne,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne,
        totalVertexPerm_tail, q2TailStabilizerPerm_blockZero]
      change tailVertex
          (ProfileDTripleJoinReduction.blockVertex 0
            (u15StabilizerEquiv .support7
              (q2VertexActionIndex first firstAction)
              ((support first).embedding position)).val) =
        (coordinatesFor first second).vertex
          (matrixBlockPerm (Equiv.refl _)
            (q2SupportActionEquiv first firstAction)
            (q2SupportActionEquiv second secondAction)
            (blockVertex 1 position))
      rw [matrixBlockPerm_blockOne,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne,
        q2Stabilizer_canonicalEmbedding]
      simp [coordinatesFor]
      rfl
  · rw [threeFiveEquiv_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo,
      totalVertexPerm_tail, q2TailStabilizerPerm_blockOne]
    change tailVertex
        (ProfileDTripleJoinReduction.blockVertex 1
          (u15StabilizerEquiv .support7
            (q2VertexActionIndex second secondAction)
            ((support second).embedding position)).val) =
      (coordinatesFor first second).vertex
        (matrixBlockPerm (Equiv.refl _)
          (q2SupportActionEquiv first firstAction)
          (q2SupportActionEquiv second secondAction)
          (blockVertex 2 position))
    rw [matrixBlockPerm_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo,
      q2Stabilizer_canonicalEmbedding]
    simp [coordinatesFor]
    rfl

noncomputable def combinedMatrixPerm
    (first second : SupportRepresentative) (a0 a1 a2 : Fin 10) :
    Equiv.Perm (Fin 15) :=
  matrixBlockPerm (freeActionEquiv a0)
    (q2SupportActionEquiv first a1)
    (q2SupportActionEquiv second a2)

theorem freeMatrixPerm_q2TailMatrixPerm
    (first second : SupportRepresentative) (a0 a1 a2 : Fin 10)
    (i : Fin 15) :
    freeMatrixPerm a0 (q2TailMatrixPerm first second a1 a2 i) =
      combinedMatrixPerm first second a0 a1 a2 i := by
  change
    matrixBlockPerm (freeActionEquiv a0) (Equiv.refl _) (Equiv.refl _)
        (matrixBlockPerm (Equiv.refl _)
          (q2SupportActionEquiv first a1)
          (q2SupportActionEquiv second a2) i) =
      matrixBlockPerm (freeActionEquiv a0)
        (q2SupportActionEquiv first a1)
        (q2SupportActionEquiv second a2) i
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixBlockPerm_blockZero,
        matrixBlockPerm_blockZero, matrixBlockPerm_blockZero]
      rfl
    · rw [threeFiveEquiv_blockOne, matrixBlockPerm_blockOne,
        matrixBlockPerm_blockOne, matrixBlockPerm_blockOne]
      rfl
  · rw [threeFiveEquiv_blockTwo, matrixBlockPerm_blockTwo,
      matrixBlockPerm_blockTwo, matrixBlockPerm_blockTwo]
    rfl

def alignedPosition (first second : SupportRepresentative)
    (block : Fin 3) (position : Fin 5) : Fin 5 :=
  match block.val with
  | 0 => position
  | 1 => firstLocalAlignment first position
  | _ => secondLocalAlignment second position

theorem alignedCatalogVertex_blockVertex
    (first second : SupportRepresentative) (block : Fin 3)
    (position : Fin 5) :
    alignedCatalogVertex first second (blockVertex block position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex block
        (alignedPosition first second block position) := by
  fin_cases block <;> cases first <;> cases second <;>
    fin_cases position <;> decide

theorem firstLocalAlignmentInverse_apply
    (supportRepresentative : SupportRepresentative) (position : Fin 5) :
    firstLocalAlignmentInverse supportRepresentative
        (firstLocalAlignment supportRepresentative position) = position := by
  cases supportRepresentative <;> fin_cases position <;> decide

theorem secondLocalAlignmentInverse_apply
    (supportRepresentative : SupportRepresentative) (position : Fin 5) :
    secondLocalAlignmentInverse supportRepresentative
        (secondLocalAlignment supportRepresentative position) = position := by
  cases supportRepresentative <;> fin_cases position <;> decide

theorem firstLocalAlignment_q2SupportActionEquiv
    (supportRepresentative : SupportRepresentative) (action : Fin 10)
    (position : Fin 5) :
    firstLocalAlignment supportRepresentative
        (q2SupportActionEquiv supportRepresentative action position) =
      alignedFirstAction supportRepresentative action
        (firstLocalAlignment supportRepresentative position) := by
  cases supportRepresentative <;> fin_cases action <;> fin_cases position <;>
    decide

theorem secondLocalAlignment_q2SupportActionEquiv
    (supportRepresentative : SupportRepresentative) (action : Fin 10)
    (position : Fin 5) :
    secondLocalAlignment supportRepresentative
        (q2SupportActionEquiv supportRepresentative action position) =
      alignedSecondAction supportRepresentative action
        (secondLocalAlignment supportRepresentative position) := by
  cases supportRepresentative <;> fin_cases action <;> fin_cases position <;>
    decide

theorem alignedCatalogVertex_combinedMatrixPerm_blockVertex
    (first second : SupportRepresentative) (a0 a1 a2 : Fin 10)
    (block : Fin 3) (position : Fin 5) :
    alignedCatalogVertex first second
        (combinedMatrixPerm first second a0 a1 a2
          (blockVertex block position)) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex block
        (pairBlockAction (pairOfRepresentatives first second) a0 a1 a2 block
          (alignedPosition first second block position)) := by
  by_cases hzero : block = 0
  · subst block
    simp only [combinedMatrixPerm, pairBlockAction, alignedPosition,
      pairFirst_pairOfRepresentatives, pairSecond_pairOfRepresentatives]
    rw [matrixBlockPerm_blockZero, alignedCatalogVertex_blockVertex]
    rfl
  by_cases hone : block = 1
  · subst block
    simp only [combinedMatrixPerm, pairBlockAction, alignedPosition,
      pairFirst_pairOfRepresentatives, pairSecond_pairOfRepresentatives]
    rw [matrixBlockPerm_blockOne, alignedCatalogVertex_blockVertex]
    simpa [alignedPosition, pairBlockAction] using
      congrArg
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex (1 : Fin 3))
        (firstLocalAlignment_q2SupportActionEquiv first a1 position)
  · have htwo : block = 2 := by
      fin_cases block <;> simp_all
    subst block
    simp only [combinedMatrixPerm, pairBlockAction, alignedPosition,
      pairSecond_pairOfRepresentatives]
    rw [matrixBlockPerm_blockTwo, alignedCatalogVertex_blockVertex]
    simpa [alignedPosition, pairBlockAction] using
      congrArg
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex (2 : Fin 3))
        (secondLocalAlignment_q2SupportActionEquiv second a2 position)

noncomputable def combinedRelabeledBlockTwoCatalogMatrix
    (first second : SupportRepresentative) (row : Fin 600)
    (a0 a1 a2 : Fin 10) : EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring (blockTwoCatalogMatrix first second row)
    (combinedMatrixPerm first second a0 a1 a2)

theorem orbitEquation_all_block_orientations
    (first second : SupportRepresentative) (row representative : Fin 600)
    (a0 a1 a2 : Fin 10)
    (horbit : ∀ leftBlock rightBlock : Fin 3, leftBlock < rightBlock →
      ∀ left right : Fin 5,
        catalogMatrixColor (catalogSupportKind first) row
            (blockVertex leftBlock
              (pairBlockAction (pairOfRepresentatives first second)
                a0 a1 a2 leftBlock left))
            (blockVertex rightBlock
              (pairBlockAction (pairOfRepresentatives first second)
                a0 a1 a2 rightBlock right)) =
          catalogMatrixColor (catalogSupportKind first) representative
            (blockVertex leftBlock left) (blockVertex rightBlock right))
    (leftBlock rightBlock : Fin 3) (hblocks : leftBlock ≠ rightBlock)
    (left right : Fin 5) :
    combinedRelabeledBlockTwoCatalogMatrix first second row a0 a1 a2
        (blockVertex leftBlock left) (blockVertex rightBlock right) =
      blockTwoCatalogMatrix first second representative
        (blockVertex leftBlock left) (blockVertex rightBlock right) := by
  change catalogToBlockTwoColorEquiv
      (catalogMatrixColor (catalogSupportKind first) row
        (alignedCatalogVertex first second
          (combinedMatrixPerm first second a0 a1 a2
            (blockVertex leftBlock left)))
        (alignedCatalogVertex first second
          (combinedMatrixPerm first second a0 a1 a2
            (blockVertex rightBlock right)))) =
    catalogToBlockTwoColorEquiv
      (catalogMatrixColor (catalogSupportKind first) representative
        (alignedCatalogVertex first second (blockVertex leftBlock left))
        (alignedCatalogVertex first second (blockVertex rightBlock right)))
  rw [alignedCatalogVertex_combinedMatrixPerm_blockVertex,
    alignedCatalogVertex_combinedMatrixPerm_blockVertex,
    alignedCatalogVertex_blockVertex, alignedCatalogVertex_blockVertex]
  apply congrArg catalogToBlockTwoColorEquiv
  by_cases hlt : leftBlock < rightBlock
  · exact horbit leftBlock rightBlock hlt
      (alignedPosition first second leftBlock left)
      (alignedPosition first second rightBlock right)
  · have hgt : rightBlock < leftBlock := by
      exact lt_of_le_of_ne (not_lt.mp hlt) hblocks.symm
    calc
      catalogMatrixColor (catalogSupportKind first) row
          (blockVertex leftBlock
            (pairBlockAction (pairOfRepresentatives first second)
              a0 a1 a2 leftBlock
              (alignedPosition first second leftBlock left)))
          (blockVertex rightBlock
            (pairBlockAction (pairOfRepresentatives first second)
              a0 a1 a2 rightBlock
              (alignedPosition first second rightBlock right))) =
        catalogMatrixColor (catalogSupportKind first) row
          (blockVertex rightBlock
            (pairBlockAction (pairOfRepresentatives first second)
              a0 a1 a2 rightBlock
              (alignedPosition first second rightBlock right)))
          (blockVertex leftBlock
            (pairBlockAction (pairOfRepresentatives first second)
              a0 a1 a2 leftBlock
              (alignedPosition first second leftBlock left))) :=
        catalogMatrixColor_symm _ _ _ _
      _ = catalogMatrixColor (catalogSupportKind first) representative
          (blockVertex rightBlock
            (alignedPosition first second rightBlock right))
          (blockVertex leftBlock
            (alignedPosition first second leftBlock left)) :=
        horbit rightBlock leftBlock hgt
          (alignedPosition first second rightBlock right)
          (alignedPosition first second leftBlock left)
      _ = catalogMatrixColor (catalogSupportKind first) representative
          (blockVertex leftBlock
            (alignedPosition first second leftBlock left))
          (blockVertex rightBlock
            (alignedPosition first second rightBlock right)) :=
        catalogMatrixColor_symm _ _ _ _

theorem edgeColoringEquation_on_cross_indices
    (source target : EdgeColoring (Fin 15) (Fin 4))
    (hequation : ∀ leftBlock rightBlock : Fin 3,
      leftBlock ≠ rightBlock → ∀ left right : Fin 5,
        source (blockVertex leftBlock left) (blockVertex rightBlock right) =
          target (blockVertex leftBlock left) (blockVertex rightBlock right))
    (left right : Fin 15) (hgroups : left.val / 5 ≠ right.val / 5) :
    source left right = target left right := by
  rw [← threeFiveEquiv.apply_symm_apply left,
    ← threeFiveEquiv.apply_symm_apply right] at hgroups ⊢
  generalize threeFiveEquiv.symm left = leftCoordinate at hgroups ⊢
  generalize threeFiveEquiv.symm right = rightCoordinate at hgroups ⊢
  rcases leftCoordinate with leftPart | leftPosition
  · rcases leftPart with leftPosition | leftPosition
    · rcases rightCoordinate with rightPart | rightPosition
      · rcases rightPart with rightPosition | rightPosition
        · exfalso
          rw [threeFiveEquiv_blockZero, threeFiveEquiv_blockZero] at hgroups
          apply hgroups
          rw [catalogBlockVertex_group, catalogBlockVertex_group]
        · rw [threeFiveEquiv_blockZero, threeFiveEquiv_blockOne]
          exact hequation 0 1 (by decide) leftPosition rightPosition
      · rw [threeFiveEquiv_blockZero, threeFiveEquiv_blockTwo]
        exact hequation 0 2 (by decide) leftPosition rightPosition
    · rcases rightCoordinate with rightPart | rightPosition
      · rcases rightPart with rightPosition | rightPosition
        · rw [threeFiveEquiv_blockOne, threeFiveEquiv_blockZero]
          exact hequation 1 0 (by decide) leftPosition rightPosition
        · exfalso
          rw [threeFiveEquiv_blockOne, threeFiveEquiv_blockOne] at hgroups
          apply hgroups
          rw [catalogBlockVertex_group, catalogBlockVertex_group]
      · rw [threeFiveEquiv_blockOne, threeFiveEquiv_blockTwo]
        exact hequation 1 2 (by decide) leftPosition rightPosition
  · rcases rightCoordinate with rightPart | rightPosition
    · rcases rightPart with rightPosition | rightPosition
      · rw [threeFiveEquiv_blockTwo, threeFiveEquiv_blockZero]
        exact hequation 2 0 (by decide) leftPosition rightPosition
      · rw [threeFiveEquiv_blockTwo, threeFiveEquiv_blockOne]
        exact hequation 2 1 (by decide) leftPosition rightPosition
    · exfalso
      rw [threeFiveEquiv_blockTwo, threeFiveEquiv_blockTwo] at hgroups
      apply hgroups
      rw [catalogBlockVertex_group, catalogBlockVertex_group]

theorem orbitEquation_on_cross_indices
    (first second : SupportRepresentative) (row representative : Fin 600)
    (a0 a1 a2 : Fin 10)
    (horbit : ∀ leftBlock rightBlock : Fin 3, leftBlock < rightBlock →
      ∀ left right : Fin 5,
        catalogMatrixColor (catalogSupportKind first) row
            (blockVertex leftBlock
              (pairBlockAction (pairOfRepresentatives first second)
                a0 a1 a2 leftBlock left))
            (blockVertex rightBlock
              (pairBlockAction (pairOfRepresentatives first second)
                a0 a1 a2 rightBlock right)) =
          catalogMatrixColor (catalogSupportKind first) representative
            (blockVertex leftBlock left) (blockVertex rightBlock right))
    (left right : Fin 15) (hgroups : left.val / 5 ≠ right.val / 5) :
    combinedRelabeledBlockTwoCatalogMatrix first second row a0 a1 a2
        left right =
      blockTwoCatalogMatrix first second representative left right := by
  exact edgeColoringEquation_on_cross_indices _ _
    (orbitEquation_all_block_orientations first second row representative
      a0 a1 a2 horbit) left right hgroups

noncomputable def normalizeCatalogExactToRepresentative
    (first second : SupportRepresentative) (row representative : Fin 600)
    (exact : ExactDegreeTenMatrixBranch .uut 2 SelectedPosition
      (coordinatesFor first second)
      (blockTwoCatalogMatrix first second row))
    (a0 a1 a2 : Fin 10)
    (horbit : ∀ leftBlock rightBlock : Fin 3, leftBlock < rightBlock →
      ∀ left right : Fin 5,
        catalogMatrixColor (catalogSupportKind first) row
            (blockVertex leftBlock
              (pairBlockAction (pairOfRepresentatives first second)
                a0 a1 a2 leftBlock left))
            (blockVertex rightBlock
              (pairBlockAction (pairOfRepresentatives first second)
                a0 a1 a2 rightBlock right)) =
          catalogMatrixColor (catalogSupportKind first) representative
            (blockVertex leftBlock left) (blockVertex rightBlock right)) :
    ExactDegreeTenMatrixBranch .uut 2 SelectedPosition
      (coordinatesFor first second)
      (blockTwoCatalogMatrix first second representative) :=
  let freeExact := relabelCatalogExactByFreeAction first second row exact a0
  transportExactDegreeTenMatrixBranch freeExact
    (q2TailStabilizerPerm first second a1 a2)
    (q2TailStabilizer_templateCanonical
      freeExact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      first second a1 a2)
    (by rw [q2TailStabilizerPerm_blockTwo first second])
    (u15StabilizerEquiv .support7 (q2VertexActionIndex first a1))
    (u15StabilizerEquiv .support7 (q2VertexActionIndex second a2))
    (q2TailMatrixPerm first second a1 a2)
    (q2TailStabilizerPerm_blockZero first second a1 a2)
    (q2TailStabilizerPerm_blockOne first second a1 a2)
    (q2Stabilizer_positions first a1)
    (q2Stabilizer_positions second a2)
    (q2TailMatrixPerm_coordinates_covariant first second a1 a2)
    (matrixBlockPerm_preserves_cross_group _ _ _)
    (by
      intro left right hgroups
      change blockTwoCatalogMatrix first second row
          (freeMatrixPerm a0
            (q2TailMatrixPerm first second a1 a2 left))
          (freeMatrixPerm a0
            (q2TailMatrixPerm first second a1 a2 right)) =
        blockTwoCatalogMatrix first second representative left right
      rw [freeMatrixPerm_q2TailMatrixPerm,
        freeMatrixPerm_q2TailMatrixPerm]
      exact orbitEquation_on_cross_indices first second row representative
        a0 a1 a2 horbit left right hgroups)

theorem exists_representativeCatalogExactBranch
    (pair : Fin 9) (row : Fin 600)
    (exact : ExactDegreeTenMatrixBranch .uut 2 SelectedPosition
      (coordinatesFor (pairFirst pair) (pairSecond pair))
      (blockTwoCatalogMatrix (pairFirst pair) (pairSecond pair) row)) :
    ∃ representative ∈ representativeSet pair,
      Nonempty (ExactDegreeTenMatrixBranch .uut 2 SelectedPosition
        (coordinatesFor (pairFirst pair) (pairSecond pair))
        (blockTwoCatalogMatrix (pairFirst pair) (pairSecond pair)
          representative)) := by
  obtain ⟨representative, hrep, a0, a1, a2, horbit⟩ :=
    exists_catalog_normalization pair row
  have hpair :
      pairOfRepresentatives (pairFirst pair) (pairSecond pair) = pair := by
    fin_cases pair <;> rfl
  refine ⟨representative, hrep, ?_⟩
  refine ⟨normalizeCatalogExactToRepresentative
    (pairFirst pair) (pairSecond pair) row representative exact a0 a1 a2 ?_⟩
  simpa [hpair]

#print axioms q2Stabilizer_canonicalEmbedding
#print axioms q2TailStabilizer_templateCanonical
#print axioms normalizeCatalogExactToRepresentative
#print axioms exists_representativeCatalogExactBranch

end UUTD10OrbitTransport
end R4333
