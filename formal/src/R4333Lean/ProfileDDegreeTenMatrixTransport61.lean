import R4333Lean.ProfileDUUUFiveSupportPositionSymmetry
import R4333Lean.ProfileDDegreeTenMatrixCNF

/-!
# Reusable tail-permutation transport for degree-ten matrix branches

This module lifts the existing certified five-row tail transport to the two
semantic objects used at the degree-ten matrix boundary:

* a `CanonicalBranch`, with the selected tail vertex fixed; and
* an `ExactDegreeTenMatrixBranch`, while allowing both ordered supports and
  the labelled `Fin 15` matrix coordinates to change.

The second constructor states all coordinate covariance hypotheses
explicitly.  Consequently a later support/catalogue quotient only has to
provide concrete local permutations and their checked matrix equation; the
Ramsey-semantic fields are transported here once and for all.
-/

namespace R4333
namespace ProfileDDegreeTenMatrixTransport61

open ColoringJoinRows
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDDegreeTenMatrixCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FiveExtension := ProfileDHighOwnFiveRowSplit61.FiveExtension
abbrev DegreeFlooredFiveExtension :=
  ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex

/-! ## The induced permutation of the joined 5+46 vertex set -/

def totalDecompEquiv : TotalVertex ≃ Sum FiveVertex TailVertex where
  toFun := splitVertex
  invFun := mergeVertex
  left_inv := mergeVertex_splitVertex
  right_inv := by
    intro vertex
    cases vertex <;> simp [mergeVertex]

@[simp] theorem splitVertex_mergeVertex
    (vertex : Sum FiveVertex TailVertex) :
    splitVertex (mergeVertex vertex) = vertex := by
  cases vertex <;> simp [mergeVertex]

noncomputable def totalVertexPerm (perm : Equiv.Perm TailVertex) :
    Equiv.Perm TotalVertex :=
  totalDecompEquiv.trans
    ((Equiv.sumCongr (Equiv.refl FiveVertex) perm).trans
      totalDecompEquiv.symm)

@[simp] theorem totalVertexPerm_free (perm : Equiv.Perm TailVertex)
    (a : FiveVertex) :
    totalVertexPerm perm (freeVertex a) = freeVertex a := by
  simp [totalVertexPerm, totalDecompEquiv, mergeVertex]

@[simp] theorem totalVertexPerm_tail (perm : Equiv.Perm TailVertex)
    (x : TailVertex) :
    totalVertexPerm perm (tailVertex x) = tailVertex (perm x) := by
  simp [totalVertexPerm, totalDecompEquiv, mergeVertex]

/-! ## Canonical five-row branches -/

noncomputable def transportCanonicalBranchByTailPerm
    {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (perm (blockVertex target left))
          (perm (blockVertex target right)) =
        SingleRootStarCNF.canonicalPalette (Fin.succ target)
          (SingleRootStarCNF.templateColor (blockSize target) (kind.twisted target)
            left right))
    (hselected : perm (blockVertex block position.val) =
      blockVertex block position.val) :
    CanonicalBranch kind block position where
  toDegreeFlooredFiveExtension :=
    transportDegreeFlooredFiveByTailPerm
      branch.toDegreeFlooredFiveExtension perm hcanonical
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      (perm (blockVertex block position.val)) = blockRootColor block
    rw [hselected]
    exact branch.allFiveOwn row
  insideCanonical := branch.insideCanonical
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring perm)
      (blockRootColor block) (blockVertex block position.val)
    rw [colorDegree_relabelVertices, hselected]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring perm)
      (blockRootColor block) (blockVertex block position.val) ≤ 10
    rw [colorDegree_relabelVertices, hselected]
    exact branch.tailOwnDegreeUpper

theorem totalColoring_transportCanonicalBranchByTailPerm
    {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (perm (blockVertex target left))
          (perm (blockVertex target right)) =
        SingleRootStarCNF.canonicalPalette (Fin.succ target)
          (SingleRootStarCNF.templateColor (blockSize target) (kind.twisted target)
            left right))
    (hselected : perm (blockVertex block position.val) =
      blockVertex block position.val)
    (left right : TotalVertex) :
    totalColoring
        (transportCanonicalBranchByTailPerm branch perm hcanonical hselected).toDegreeFlooredFiveExtension.toFiveExtension
        left right =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (totalVertexPerm perm left) (totalVertexPerm perm right) := by
  rw [← mergeVertex_splitVertex left, ← mergeVertex_splitVertex right]
  generalize hleft : splitVertex left = leftPart
  generalize hright : splitVertex right = rightPart
  cases leftPart <;> cases rightPart <;>
    simp [transportCanonicalBranchByTailPerm,
      transportDegreeFlooredFiveByTailPerm,
      transportFiveExtensionByTailPerm, totalVertexPerm,
      ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
      relabelVertices, totalDecompEquiv, totalColoring, pullbackColoring,
      mergeVertex]

/-! ## Exact support-and-matrix branches -/

/-- Transport an exact degree-ten matrix branch through a tail permutation.

`firstPerm` and `secondPerm` describe the induced local maps on the two
foreign blocks. `matrixPerm` describes the induced relabelling of the
three consecutive five-sets.  The hypotheses record that the target ordered
supports and matrix coordinates are precisely the pullbacks under those
maps. -/
noncomputable def transportExactDegreeTenMatrixBranch
    {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    {sourceCoordinates targetCoordinates : MatrixCoordinates block}
    {sourceMatrix targetMatrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch kind block position
      sourceCoordinates sourceMatrix)
    (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (perm (blockVertex target left))
          (perm (blockVertex target right)) =
        SingleRootStarCNF.canonicalPalette (Fin.succ target)
          (SingleRootStarCNF.templateColor (blockSize target) (kind.twisted target)
            left right))
    (hselected : perm (blockVertex block position.val) =
      blockVertex block position.val)
    (firstPerm : Equiv.Perm (Fin (blockSize (firstForeignBlock block))))
    (secondPerm : Equiv.Perm (Fin (blockSize (secondForeignBlock block))))
    (matrixPerm : Equiv.Perm (Fin 15))
    (hpermFirst : ∀ p,
      perm (blockVertex (firstForeignBlock block) p.val) =
        blockVertex (firstForeignBlock block) (firstPerm p).val)
    (hpermSecond : ∀ p,
      perm (blockVertex (secondForeignBlock block) p.val) =
        blockVertex (secondForeignBlock block) (secondPerm p).val)
    (hfirstPositions : ∀ p,
      p ∈ targetCoordinates.first.positions ↔
        firstPerm p ∈ sourceCoordinates.first.positions)
    (hsecondPositions : ∀ p,
      p ∈ targetCoordinates.second.positions ↔
        secondPerm p ∈ sourceCoordinates.second.positions)
    (hmatrixCoordinates : ∀ i,
      totalVertexPerm perm (targetCoordinates.vertex i) =
        sourceCoordinates.vertex (matrixPerm i))
    (hmatrixGroups : ∀ left right,
      left.val / 5 ≠ right.val / 5 →
        (matrixPerm left).val / 5 ≠ (matrixPerm right).val / 5)
    (hmatrix : ∀ left right,
      left.val / 5 ≠ right.val / 5 →
        sourceMatrix (matrixPerm left) (matrixPerm right) =
          targetMatrix left right) :
    ExactDegreeTenMatrixBranch kind block position
      targetCoordinates targetMatrix where
  branch := transportCanonicalBranchByTailPerm
    exact.branch perm hcanonical hselected
  tailOwnDegreeTen := by
    change colorDegree
      (relabelVertices
        exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        perm) (blockRootColor block) (blockVertex block position.val) = 10
    rw [colorDegree_relabelVertices, hselected]
    exact exact.tailOwnDegreeTen
  firstSupportExact := by
    intro p
    change p ∈ targetCoordinates.first.positions ↔
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (perm (blockVertex block position.val))
        (perm (blockVertex (firstForeignBlock block) p.val)) =
          blockRootColor block
    rw [hselected, hpermFirst, hfirstPositions]
    exact exact.firstSupportExact (firstPerm p)
  secondSupportExact := by
    intro p
    change p ∈ targetCoordinates.second.positions ↔
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (perm (blockVertex block position.val))
        (perm (blockVertex (secondForeignBlock block) p.val)) =
          blockRootColor block
    rw [hselected, hpermSecond, hsecondPositions]
    exact exact.secondSupportExact (secondPerm p)
  matrixExact := by
    intro left right hgroups
    rw [totalColoring_transportCanonicalBranchByTailPerm,
      hmatrixCoordinates, hmatrixCoordinates]
    exact (exact.matrixExact (matrixPerm left) (matrixPerm right)
      (hmatrixGroups left right hgroups)).trans
        (hmatrix left right hgroups)

#print axioms
  R4333.ProfileDDegreeTenMatrixTransport61.transportCanonicalBranchByTailPerm
#print axioms
  R4333.ProfileDDegreeTenMatrixTransport61.transportExactDegreeTenMatrixBranch

end ProfileDDegreeTenMatrixTransport61
end R4333
