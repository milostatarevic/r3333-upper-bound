import R4333Lean.ContinuationDegreeNineTwistedRoot1CaseFactorCNF61
import R4333Lean.ProfileDDegreeTenMatrixTransport61

/-! Continuation-authored (locks/duuu), 2026-08-05.
Twisted case (slot 3, root 1) physical-symmetry clone of
ProfileDUUUDegreeNinePhysicalSymmetry61.  Physical tables and tail/free
transports are case-independent (verbatim); the five label-side
k15Template sites are flipped false -> true; the root-1 label stabilizer
is trivial, so the rootFlip section and the RootStabilizer import/open
are dropped. -/

/-!
# Physical symmetry transport for the twisted root-1 UUU degree-nine case

The selected vertex is the last vertex of the `K16` block.  The two foreign
`K15` blocks may therefore be relabelled independently by strong `K15`
automorphisms, while the retained free five-cycle may be relabelled by any
of its automorphisms.  This file lifts those three independent operations to
the complete 51-vertex canonical branch and records exact colour covariance.
-/

namespace R4333
namespace ContinuationDegreeNineTwistedRoot1PhysicalSymmetry61

open ColoringJoinRows
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixTransport61
open ContinuationDegreeNineTwistedRoot1Case61
open ContinuationDegreeNineTwistedRoot1CaseCNF61
open ContinuationDegreeNineTwistedRoot1CaseFactorCNF61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex

/-! ## Lightweight free-cycle transport

These generic transport definitions used to be obtained incidentally through
the degree-ten end-to-end semantic module.  They need only the canonical
branch and matrix-transport interfaces imported above, so keeping local copies
here avoids making degree-nine symmetry depend on the complete degree-ten
catalogue certificate.
-/

noncomputable def totalFreeVertexPerm
    (perm : Equiv.Perm FiveVertex) : Equiv.Perm TotalVertex :=
  totalDecompEquiv.trans
    ((Equiv.sumCongr perm (Equiv.refl TailVertex)).trans
      totalDecompEquiv.symm)

@[simp] theorem totalFreeVertexPerm_free
    (perm : Equiv.Perm FiveVertex) (a : FiveVertex) :
    totalFreeVertexPerm perm (freeVertex a) = freeVertex (perm a) := by
  simp [totalFreeVertexPerm, totalDecompEquiv, mergeVertex]

@[simp] theorem totalFreeVertexPerm_tail
    (perm : Equiv.Perm FiveVertex) (x : TailVertex) :
    totalFreeVertexPerm perm (tailVertex x) = tailVertex x := by
  simp [totalFreeVertexPerm, totalDecompEquiv, mergeVertex]

noncomputable def transportCanonicalBranchByFreePerm
    {kind : ProfileDTripleJoinReduction.Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (perm : Equiv.Perm FiveVertex)
    (hinside : ∀ a b, a ≠ b →
      branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (perm a) (perm b) =
        decodeRemainingColor block (!canonicalCycleWord.coloring a b)) :
    CanonicalBranch kind block position where
  toDegreeFlooredFiveExtension :=
    transportDegreeFlooredFiveExtension perm
      branch.toDegreeFlooredFiveExtension
  allFiveOwn := by
    intro a
    exact branch.allFiveOwn (perm a)
  insideCanonical := hinside
  tailOwnDegreeLower := branch.tailOwnDegreeLower
  tailOwnDegreeUpper := branch.tailOwnDegreeUpper

theorem totalColoring_transportCanonicalBranchByFreePerm
    {kind : ProfileDTripleJoinReduction.Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (perm : Equiv.Perm FiveVertex)
    (hinside : ∀ a b, a ≠ b →
      branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (perm a) (perm b) =
        decodeRemainingColor block (!canonicalCycleWord.coloring a b))
    (left right : TotalVertex) :
    totalColoring
        (transportCanonicalBranchByFreePerm branch perm hinside).toDegreeFlooredFiveExtension.toFiveExtension
        left right =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (totalFreeVertexPerm perm left) (totalFreeVertexPerm perm right) := by
  rw [← mergeVertex_splitVertex left, ← mergeVertex_splitVertex right]
  generalize splitVertex left = leftPart
  generalize splitVertex right = rightPart
  cases leftPart <;> cases rightPart <;>
    simp [transportCanonicalBranchByFreePerm,
      transportDegreeFlooredFiveExtension, transportFiveExtension,
      totalFreeVertexPerm, totalDecompEquiv, totalColoring,
      pullbackColoring, mergeVertex]

/-! ## The two independent physical `K15` actions -/

def physicalK15Map : Fin 10 → Fin 15 → Fin 15 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ![5, 9, 2, 14, 12, 0, 11, 7, 13, 1, 10, 6, 4, 8, 3],
    ![7, 6, 4, 5, 2, 3, 1, 0, 8, 9, 11, 10, 13, 12, 14],
    ![3, 9, 4, 14, 13, 7, 10, 0, 12, 6, 11, 1, 2, 8, 5],
    ![5, 10, 8, 7, 12, 3, 1, 14, 4, 11, 9, 6, 13, 2, 0],
    ![3, 11, 8, 0, 13, 5, 6, 14, 2, 10, 9, 1, 12, 4, 7],
    ![7, 11, 12, 0, 2, 14, 9, 5, 13, 1, 6, 10, 8, 4, 3],
    ![14, 1, 12, 3, 8, 7, 10, 5, 4, 11, 6, 9, 2, 13, 0],
    ![0, 10, 13, 7, 4, 14, 9, 3, 12, 6, 1, 11, 8, 2, 5],
    ![14, 6, 13, 5, 8, 0, 11, 3, 2, 10, 1, 9, 4, 12, 7]]

theorem physicalK15Map_bijective (action : Fin 10) :
    Function.Bijective (physicalK15Map action) := by
  fin_cases action <;> decide

theorem physicalK15Map_preserves :
    ∀ (action : Fin 10) (left right : Fin 15), left ≠ right →
      k15Template false (physicalK15Map action left)
          (physicalK15Map action right) =
        k15Template false left right := by
  decide

noncomputable def physicalK15Equiv (action : Fin 10) :
    Equiv.Perm (Fin 15) :=
  Equiv.ofBijective (physicalK15Map action)
    (physicalK15Map_bijective action)

theorem physicalK15Equiv_preserves
    (action : Fin 10) (left right : Fin 15) (hne : left ≠ right) :
    k15Template false (physicalK15Equiv action left)
        (physicalK15Equiv action right) =
      k15Template false left right := by
  change k15Template false
      (physicalK15Map action left)
      (physicalK15Map action right) =
    k15Template false left right
  exact physicalK15Map_preserves action left right hne

theorem physicalK15Equiv_symm_preserves
    (action : Fin 10) (left right : Fin 15) (hne : left ≠ right) :
    k15Template false ((physicalK15Equiv action).symm left)
        ((physicalK15Equiv action).symm right) =
      k15Template false left right := by
  have h := physicalK15Equiv_preserves action
    ((physicalK15Equiv action).symm left)
    ((physicalK15Equiv action).symm right)
    ((physicalK15Equiv action).symm.injective.ne hne)
  simpa using h.symm

/-! ## Tail transport: inverse pullback on blocks zero and one -/

noncomputable def degreeNineTailPerm
    (smallAction largeAction : Fin 10) : Equiv.Perm TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr (physicalK15Equiv smallAction).symm
        (physicalK15Equiv largeAction).symm)
      (Equiv.refl (Fin 16))).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

@[simp] theorem degreeNineTailPerm_blockZero
    (smallAction largeAction : Fin 10) (position : Fin 15) :
    degreeNineTailPerm smallAction largeAction
        (ProfileDTripleJoinReduction.blockVertex 0 position.val) =
      ProfileDTripleJoinReduction.blockVertex 0
        ((physicalK15Equiv smallAction).symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp only [degreeNineTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero _

@[simp] theorem degreeNineTailPerm_blockOne
    (smallAction largeAction : Fin 10) (position : Fin 15) :
    degreeNineTailPerm smallAction largeAction
        (ProfileDTripleJoinReduction.blockVertex 1 position.val) =
      ProfileDTripleJoinReduction.blockVertex 1
        ((physicalK15Equiv largeAction).symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp only [degreeNineTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne _

@[simp] theorem degreeNineTailPerm_blockTwo
    (smallAction largeAction : Fin 10) (position : Fin 16) :
    degreeNineTailPerm smallAction largeAction
        (ProfileDTripleJoinReduction.blockVertex 2 position.val) =
      ProfileDTripleJoinReduction.blockVertex 2 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp [degreeNineTailPerm]

theorem degreeNineTailPerm_templateCanonical
    (tail : ProfileDTripleJoinReduction.Witness .uuu)
    (smallAction largeAction : Fin 10) :
    ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      tail.coloring
          (degreeNineTailPerm smallAction largeAction
            (ProfileDTripleJoinReduction.blockVertex target left))
          (degreeNineTailPerm smallAction largeAction
            (ProfileDTripleJoinReduction.blockVertex target right)) =
        SingleRootStarCNF.canonicalPalette (Fin.succ target)
          (SingleRootStarCNF.templateColor (blockSize target)
            (Kind.twisted .uuu target) left right) := by
  intro target left right hleft hright hlr
  fin_cases target
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (degreeNineTailPerm smallAction largeAction
            (ProfileDTripleJoinReduction.blockVertex 0 left))
          (degreeNineTailPerm smallAction largeAction
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
      degreeNineTailPerm_blockZero,
      show ProfileDTripleJoinReduction.blockVertex 0 right =
        ProfileDTripleJoinReduction.blockVertex 0 rightFin.val by rfl,
      degreeNineTailPerm_blockZero]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 0 (by decide)
          ((physicalK15Equiv smallAction).symm leftFin)
          ((physicalK15Equiv smallAction).symm rightFin)
          ((physicalK15Equiv smallAction).symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (0 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 0
            ((physicalK15Equiv smallAction).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 0
            ((physicalK15Equiv smallAction).symm rightFin).val) =
        SingleRootStarCNF.canonicalPalette 1
          (k15Template false
            ((physicalK15Equiv smallAction).symm leftFin)
            ((physicalK15Equiv smallAction).symm rightFin)) := by
              simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 1
          (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 1)
          (physicalK15Equiv_symm_preserves smallAction leftFin rightFin hne)
      _ = SingleRootStarCNF.canonicalPalette 1
          (SingleRootStarCNF.templateColor 15 false left right) := by
        simp [SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (degreeNineTailPerm smallAction largeAction
            (ProfileDTripleJoinReduction.blockVertex 1 left))
          (degreeNineTailPerm smallAction largeAction
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
      degreeNineTailPerm_blockOne,
      show ProfileDTripleJoinReduction.blockVertex 1 right =
        ProfileDTripleJoinReduction.blockVertex 1 rightFin.val by rfl,
      degreeNineTailPerm_blockOne]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 1 (by decide)
          ((physicalK15Equiv largeAction).symm leftFin)
          ((physicalK15Equiv largeAction).symm rightFin)
          ((physicalK15Equiv largeAction).symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (1 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1
            ((physicalK15Equiv largeAction).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 1
            ((physicalK15Equiv largeAction).symm rightFin).val) =
        SingleRootStarCNF.canonicalPalette 2
          (k15Template false
            ((physicalK15Equiv largeAction).symm leftFin)
            ((physicalK15Equiv largeAction).symm rightFin)) := by
              simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 2
          (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 2)
          (physicalK15Equiv_symm_preserves largeAction leftFin rightFin hne)
      _ = SingleRootStarCNF.canonicalPalette 2
          (SingleRootStarCNF.templateColor 15 false left right) := by
        simp [SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 16 at hleft
    change right < 16 at hright
    change
      tail.coloring
          (degreeNineTailPerm smallAction largeAction
            (ProfileDTripleJoinReduction.blockVertex 2 left))
          (degreeNineTailPerm smallAction largeAction
            (ProfileDTripleJoinReduction.blockVertex 2 right)) =
        SingleRootStarCNF.canonicalPalette 3
          (SingleRootStarCNF.templateColor 16 false left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 2 left =
        ProfileDTripleJoinReduction.blockVertex 2 leftFin.val by rfl,
      degreeNineTailPerm_blockTwo,
      show ProfileDTripleJoinReduction.blockVertex 2 right =
        ProfileDTripleJoinReduction.blockVertex 2 rightFin.val by rfl,
      degreeNineTailPerm_blockTwo]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        tail 2 (by decide) leftFin rightFin hne
    have htwisted : Kind.uuu.twisted (2 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    simpa [SingleRootStarCNF.templateColor,
      SingleRootStarCNF.fin16, leftFin, rightFin,
      Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using hedge

noncomputable def transportBranchByPhysicalK15
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (smallAction largeAction : Fin 10) :
    CanonicalBranch .uuu 2 (Fin.last 15) :=
  transportCanonicalBranchByTailPerm branch
    (degreeNineTailPerm smallAction largeAction)
    (degreeNineTailPerm_templateCanonical
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      smallAction largeAction)
    (by rw [degreeNineTailPerm_blockTwo])

theorem totalColoring_transportBranchByPhysicalK15
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (smallAction largeAction : Fin 10) (left right : TotalVertex) :
    totalColoring
        (transportBranchByPhysicalK15 branch smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
        left right =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (totalVertexPerm (degreeNineTailPerm smallAction largeAction) left)
        (totalVertexPerm (degreeNineTailPerm smallAction largeAction) right) := by
  exact totalColoring_transportCanonicalBranchByTailPerm branch
    (degreeNineTailPerm smallAction largeAction)
    (degreeNineTailPerm_templateCanonical
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      smallAction largeAction)
    (by rw [degreeNineTailPerm_blockTwo]) left right

/-! ## Independent relabelling of the retained free five-cycle -/

theorem physicalBranch_inside_after_freePerm
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10)
    (left right : FiveVertex) (hne : left ≠ right) :
    (transportBranchByPhysicalK15 branch smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension.inside
          (freePerm left) (freePerm right) =
      decodeRemainingColor 2 (!canonicalCycleWord.coloring left right) := by
  let physical : CanonicalBranch .uuu 2 (Fin.last 15) :=
    transportBranchByPhysicalK15 branch smallAction largeAction
  calc
    physical.toDegreeFlooredFiveExtension.toFiveExtension.inside
        (freePerm left) (freePerm right) =
      decodeRemainingColor 2
        (!canonicalCycleWord.coloring (freePerm left) (freePerm right)) :=
      physical.insideCanonical _ _ (freePerm.injective.ne hne)
    _ = _ := by rw [hcycle left right hne]

noncomputable def transportBranchByPhysicalAndFree
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10) :
    CanonicalBranch .uuu 2 (Fin.last 15) :=
  transportCanonicalBranchByFreePerm
    (transportBranchByPhysicalK15 branch smallAction largeAction)
    freePerm
    (physicalBranch_inside_after_freePerm branch freePerm hcycle
      smallAction largeAction)

theorem totalColoring_transportBranchByPhysicalAndFree
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10) (left right : TotalVertex) :
    totalColoring
        (transportBranchByPhysicalAndFree branch freePerm hcycle
          smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
        left right =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (totalVertexPerm (degreeNineTailPerm smallAction largeAction)
          (totalFreeVertexPerm freePerm left))
        (totalVertexPerm (degreeNineTailPerm smallAction largeAction)
          (totalFreeVertexPerm freePerm right)) := by
  unfold transportBranchByPhysicalAndFree
  calc
    _ = totalColoring
          (transportBranchByPhysicalK15 branch smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
          (totalFreeVertexPerm freePerm left)
          (totalFreeVertexPerm freePerm right) :=
      totalColoring_transportCanonicalBranchByFreePerm
        (transportBranchByPhysicalK15 branch smallAction largeAction)
        freePerm
        (physicalBranch_inside_after_freePerm branch freePerm hcycle
          smallAction largeAction) left right
    _ = _ := totalColoring_transportBranchByPhysicalK15 branch
      smallAction largeAction
      (totalFreeVertexPerm freePerm left)
      (totalFreeVertexPerm freePerm right)

theorem totalColoring_transport_selected_blockOne
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10) (position : Fin 15) :
    totalColoring
        (transportBranchByPhysicalAndFree branch freePerm hcycle
          smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex (physicalBlockOneVertex position) =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex
        (physicalBlockOneVertex
          ((physicalK15Equiv largeAction).symm position)) := by
  rw [totalColoring_transportBranchByPhysicalAndFree]
  change totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
      (totalVertexPerm (degreeNineTailPerm smallAction largeAction)
        (totalFreeVertexPerm freePerm
          (tailVertex (ProfileDTripleJoinReduction.blockVertex 2 15))))
      (totalVertexPerm (degreeNineTailPerm smallAction largeAction)
        (totalFreeVertexPerm freePerm
          (tailVertex
            (ProfileDTripleJoinReduction.blockVertex 1 position.val)))) =
    totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
      (tailVertex (ProfileDTripleJoinReduction.blockVertex 2 15))
      (tailVertex
        (ProfileDTripleJoinReduction.blockVertex 1
          ((physicalK15Equiv largeAction).symm position).val))
  rw [totalFreeVertexPerm_tail, totalFreeVertexPerm_tail,
    totalVertexPerm_tail, totalVertexPerm_tail,
    show ProfileDTripleJoinReduction.blockVertex 2 15 =
        ProfileDTripleJoinReduction.blockVertex 2 (Fin.last 15).val by rfl,
    degreeNineTailPerm_blockTwo, degreeNineTailPerm_blockOne]

theorem totalColoring_transport_selected_blockZero
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10) (position : Fin 15) :
    totalColoring
        (transportBranchByPhysicalAndFree branch freePerm hcycle
          smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex (physicalBlockZeroVertex position) =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex
        (physicalBlockZeroVertex
          ((physicalK15Equiv smallAction).symm position)) := by
  rw [totalColoring_transportBranchByPhysicalAndFree]
  change totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
      (totalVertexPerm (degreeNineTailPerm smallAction largeAction)
        (totalFreeVertexPerm freePerm
          (tailVertex (ProfileDTripleJoinReduction.blockVertex 2 15))))
      (totalVertexPerm (degreeNineTailPerm smallAction largeAction)
        (totalFreeVertexPerm freePerm
          (tailVertex
            (ProfileDTripleJoinReduction.blockVertex 0 position.val)))) =
    totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
      (tailVertex (ProfileDTripleJoinReduction.blockVertex 2 15))
      (tailVertex
        (ProfileDTripleJoinReduction.blockVertex 0
          ((physicalK15Equiv smallAction).symm position).val))
  rw [totalFreeVertexPerm_tail, totalFreeVertexPerm_tail,
    totalVertexPerm_tail, totalVertexPerm_tail,
    show ProfileDTripleJoinReduction.blockVertex 2 15 =
        ProfileDTripleJoinReduction.blockVertex 2 (Fin.last 15).val by rfl,
    degreeNineTailPerm_blockTwo, degreeNineTailPerm_blockZero]

theorem totalColoring_transport_free_blockOne
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10)
    (free : FiveVertex) (position : Fin 15) :
    totalColoring
        (transportBranchByPhysicalAndFree branch freePerm hcycle
          smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex free) (physicalBlockOneVertex position) =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex (freePerm free))
        (physicalBlockOneVertex
          ((physicalK15Equiv largeAction).symm position)) := by
  rw [totalColoring_transportBranchByPhysicalAndFree]
  simp [physicalBlockOneVertex]

theorem totalColoring_transport_free_blockZero
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10)
    (free : FiveVertex) (position : Fin 15) :
    totalColoring
        (transportBranchByPhysicalAndFree branch freePerm hcycle
          smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex free) (physicalBlockZeroVertex position) =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex (freePerm free))
        (physicalBlockZeroVertex
          ((physicalK15Equiv smallAction).symm position)) := by
  rw [totalColoring_transportBranchByPhysicalAndFree]
  simp [physicalBlockZeroVertex]

theorem totalColoring_transport_blockOne_blockZero
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (freePerm : Equiv.Perm FiveVertex)
    (hcycle : ∀ left right : FiveVertex, left ≠ right →
      canonicalCycleWord.coloring (freePerm left) (freePerm right) =
        canonicalCycleWord.coloring left right)
    (smallAction largeAction : Fin 10)
    (large small : Fin 15) :
    totalColoring
        (transportBranchByPhysicalAndFree branch freePerm hcycle
          smallAction largeAction).toDegreeFlooredFiveExtension.toFiveExtension
        (physicalBlockOneVertex large) (physicalBlockZeroVertex small) =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (physicalBlockOneVertex
          ((physicalK15Equiv largeAction).symm large))
        (physicalBlockZeroVertex
          ((physicalK15Equiv smallAction).symm small)) := by
  rw [totalColoring_transportBranchByPhysicalAndFree]
  simp [physicalBlockOneVertex, physicalBlockZeroVertex]

/-! ## The semantic assignment predicate transported by these actions -/

structure FactorAssignmentRealization
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (free : FreeFactorChoice) (large : LargeFactorChoice)
    (small : SmallFactorChoice) : Prop where
  largeSupport : ∀ position : Fin 15,
    totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex (physicalBlockOneVertex position) = 3 ↔
      position ∈ large.support.1
  smallSupport : ∀ position : Fin 15,
    totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex (physicalBlockZeroVertex position) = 3 ↔
      position ∈ small.support.1
  freeLarge : ∀ freeIndex : Fin 5, ∀ largeIndex : Fin 5,
    totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex freeIndex)
        (physicalBlockOneVertex (large.physical largeIndex)) =
      decodedNormalHostColor
        (k15Template true (free.label freeIndex)
          (large.label largeIndex))
  freeSmall : ∀ freeIndex : Fin 5, ∀ smallIndex : Fin 4,
    totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex freeIndex)
        (physicalBlockZeroVertex (small.physical smallIndex)) =
      decodedNormalHostColor
        (k15Template true (free.label freeIndex)
          (small.label smallIndex))
  largeSmall : ∀ largeIndex : Fin 5, ∀ smallIndex : Fin 4,
    totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (physicalBlockOneVertex (large.physical largeIndex))
        (physicalBlockZeroVertex (small.physical smallIndex)) =
      decodedNormalHostColor
        (k15Template true (large.label largeIndex)
          (small.label smallIndex))

theorem semantic_factorAssignmentRealization
    (realization : TwistedRoot1Realization)
    (data : CanonicalStrongData realization) :
    FactorAssignmentRealization data.branch
      (semanticFreeFactorChoice realization data)
      (semanticLargeFactorChoice realization data)
      (semanticSmallFactorChoice realization data) where
  largeSupport := by
    intro position
    simpa [semanticLargeFactorChoice, twistedRoot1SupportPair] using
      data.blockOne_support_iff position
  smallSupport := by
    intro position
    simpa [semanticSmallFactorChoice, twistedRoot1SupportPair] using
      data.blockZero_support_iff position
  freeLarge := by
    intro freeIndex largeIndex
    simpa [semanticFreeFactorChoice_label,
      semanticLargeFactorChoice_physical,
      semanticLargeFactorChoice_label] using
        semanticAssignment_freeLarge_edge realization data
          freeIndex largeIndex
  freeSmall := by
    intro freeIndex smallIndex
    simpa [semanticFreeFactorChoice_label,
      semanticSmallFactorChoice_physical,
      semanticSmallFactorChoice_label] using
        semanticAssignment_freeSmall_edge realization data
          freeIndex smallIndex
  largeSmall := by
    intro largeIndex smallIndex
    simpa [semanticLargeFactorChoice_physical,
      semanticSmallFactorChoice_physical,
      semanticLargeFactorChoice_label,
      semanticSmallFactorChoice_label] using
        semanticAssignment_largeSmall_edge realization data
          largeIndex smallIndex

/-! ## Normalization witnesses and the general transport theorem -/

noncomputable def freeChoiceNormalizer
    (source target : FreeFactorChoice) : Equiv.Perm FiveVertex :=
  target.1.trans source.1.symm

theorem freeChoiceNormalizer_index
    (source target : FreeFactorChoice) (position : FiveVertex) :
    source.1 (freeChoiceNormalizer source target position) =
      target.1 position := by
  simp [freeChoiceNormalizer]

theorem freeChoiceNormalizer_label
    (source target : FreeFactorChoice) (position : FiveVertex) :
    source.label (freeChoiceNormalizer source target position) =
      target.label position := by
  rw [FreeFactorChoice.label, FreeFactorChoice.label,
    freeChoiceNormalizer_index]

theorem freeChoiceNormalizer_preserves_normalColor
    (source target : FreeFactorChoice)
    (left right : FiveVertex) (hne : left ≠ right) :
    twistedRoot1FreeNormalColor (freeChoiceNormalizer source target left)
        (freeChoiceNormalizer source target right) =
      twistedRoot1FreeNormalColor left right := by
  have hsource := source.2
    (freeChoiceNormalizer source target left)
    (freeChoiceNormalizer source target right)
    ((freeChoiceNormalizer source target).injective.ne hne)
  have htarget := target.2 left right hne
  change k15Template true
      (source.label (freeChoiceNormalizer source target left))
      (source.label (freeChoiceNormalizer source target right)) = _ at hsource
  change k15Template true (target.label left) (target.label right) = _
    at htarget
  rw [freeChoiceNormalizer_label, freeChoiceNormalizer_label] at hsource
  exact hsource.symm.trans htarget

theorem freeChoiceNormalizer_preserves_cycle
    (source target : FreeFactorChoice)
    (left right : FiveVertex) (hne : left ≠ right) :
    canonicalCycleWord.coloring
        (freeChoiceNormalizer source target left)
        (freeChoiceNormalizer source target right) =
      canonicalCycleWord.coloring left right := by
  have hnormal := freeChoiceNormalizer_preserves_normalColor
    source target left right hne
  unfold twistedRoot1FreeNormalColor at hnormal
  by_cases hleft : canonicalCycleWord.coloring
      (freeChoiceNormalizer source target left)
      (freeChoiceNormalizer source target right)
  · by_cases hright : canonicalCycleWord.coloring left right
    · simp [hleft, hright]
    · simp [hleft, hright] at hnormal
  · by_cases hright : canonicalCycleWord.coloring left right
    · simp [hleft, hright] at hnormal
    · simp [hleft, hright]

structure PhysicalNormalizationWitness
    (sourceLarge targetLarge : LargeFactorChoice)
    (sourceSmall targetSmall : SmallFactorChoice) where
  largeAction : Fin 10
  smallAction : Fin 10
  largePhysical : ∀ index : Fin 5,
    targetLarge.physical index =
      physicalK15Equiv largeAction (sourceLarge.physical index)
  smallPhysical : ∀ index : Fin 4,
    targetSmall.physical index =
      physicalK15Equiv smallAction (sourceSmall.physical index)
  largeSupport : ∀ position : Fin 15,
    position ∈ targetLarge.support.1 ↔
      (physicalK15Equiv largeAction).symm position ∈
        sourceLarge.support.1
  smallSupport : ∀ position : Fin 15,
    position ∈ targetSmall.support.1 ↔
      (physicalK15Equiv smallAction).symm position ∈
        sourceSmall.support.1

theorem largeFactorChoice_mem_support_iff_exists_physical
    (choice : LargeFactorChoice) (position : Fin 15) :
    position ∈ choice.support.1 ↔
      ∃ index : Fin 5, choice.physical index = position := by
  constructor
  · intro hposition
    let member : ↑choice.support.1 := ⟨position, hposition⟩
    let index : Fin 5 := choice.perm.symm
      ((largeFactorOrder choice.support).symm member)
    refine ⟨index, ?_⟩
    simp [LargeFactorChoice.physical, index, member]
  · rintro ⟨index, rfl⟩
    exact (largeFactorOrder choice.support (choice.perm index)).2

theorem smallFactorChoice_mem_support_iff_exists_physical
    (choice : SmallFactorChoice) (position : Fin 15) :
    position ∈ choice.support.1 ↔
      ∃ index : Fin 4, choice.physical index = position := by
  constructor
  · intro hposition
    let member : ↑choice.support.1 := ⟨position, hposition⟩
    let index : Fin 4 := choice.perm.symm
      ((smallFactorOrder choice.support).symm member)
    refine ⟨index, ?_⟩
    simp [SmallFactorChoice.physical, index, member]
  · rintro ⟨index, rfl⟩
    exact (smallFactorOrder choice.support (choice.perm index)).2

theorem largeSupport_transport_of_physical
    (source target : LargeFactorChoice) (action : Fin 10)
    (hphysical : ∀ index : Fin 5,
      target.physical index =
        physicalK15Equiv action (source.physical index))
    (position : Fin 15) :
    position ∈ target.support.1 ↔
      (physicalK15Equiv action).symm position ∈ source.support.1 := by
  rw [largeFactorChoice_mem_support_iff_exists_physical,
    largeFactorChoice_mem_support_iff_exists_physical]
  constructor
  · rintro ⟨index, hindex⟩
    refine ⟨index, ?_⟩
    rw [← hindex, hphysical, Equiv.symm_apply_apply]
  · rintro ⟨index, hindex⟩
    refine ⟨index, ?_⟩
    rw [hphysical, hindex, Equiv.apply_symm_apply]

theorem smallSupport_transport_of_physical
    (source target : SmallFactorChoice) (action : Fin 10)
    (hphysical : ∀ index : Fin 4,
      target.physical index =
        physicalK15Equiv action (source.physical index))
    (position : Fin 15) :
    position ∈ target.support.1 ↔
      (physicalK15Equiv action).symm position ∈ source.support.1 := by
  rw [smallFactorChoice_mem_support_iff_exists_physical,
    smallFactorChoice_mem_support_iff_exists_physical]
  constructor
  · rintro ⟨index, hindex⟩
    refine ⟨index, ?_⟩
    rw [← hindex, hphysical, Equiv.symm_apply_apply]
  · rintro ⟨index, hindex⟩
    refine ⟨index, ?_⟩
    rw [hphysical, hindex, Equiv.apply_symm_apply]

noncomputable def PhysicalNormalizationWitness.ofPhysicalEquations
    (sourceLarge targetLarge : LargeFactorChoice)
    (sourceSmall targetSmall : SmallFactorChoice)
    (largeAction smallAction : Fin 10)
    (largePhysical : ∀ index : Fin 5,
      targetLarge.physical index =
        physicalK15Equiv largeAction (sourceLarge.physical index))
    (smallPhysical : ∀ index : Fin 4,
      targetSmall.physical index =
        physicalK15Equiv smallAction (sourceSmall.physical index)) :
    PhysicalNormalizationWitness
      sourceLarge targetLarge sourceSmall targetSmall where
  largeAction := largeAction
  smallAction := smallAction
  largePhysical := largePhysical
  smallPhysical := smallPhysical
  largeSupport := largeSupport_transport_of_physical
    sourceLarge targetLarge largeAction largePhysical
  smallSupport := smallSupport_transport_of_physical
    sourceSmall targetSmall smallAction smallPhysical

noncomputable def normalizedBranch
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (sourceFree targetFree : FreeFactorChoice)
    {sourceLarge targetLarge : LargeFactorChoice}
    {sourceSmall targetSmall : SmallFactorChoice}
    (witness : PhysicalNormalizationWitness
      sourceLarge targetLarge sourceSmall targetSmall) :
    CanonicalBranch .uuu 2 (Fin.last 15) :=
  transportBranchByPhysicalAndFree branch
    (freeChoiceNormalizer sourceFree targetFree)
    (freeChoiceNormalizer_preserves_cycle sourceFree targetFree)
    witness.smallAction witness.largeAction

theorem FactorAssignmentRealization.normalize
    {branch : CanonicalBranch .uuu 2 (Fin.last 15)}
    {sourceFree targetFree : FreeFactorChoice}
    {sourceLarge targetLarge : LargeFactorChoice}
    {sourceSmall targetSmall : SmallFactorChoice}
    (realization : FactorAssignmentRealization branch
      sourceFree sourceLarge sourceSmall)
    (witness : PhysicalNormalizationWitness
      sourceLarge targetLarge sourceSmall targetSmall) :
    FactorAssignmentRealization
      (normalizedBranch branch sourceFree targetFree witness)
      targetFree targetLarge targetSmall where
  largeSupport := by
    intro position
    rw [normalizedBranch,
      totalColoring_transport_selected_blockOne]
    exact (realization.largeSupport
      ((physicalK15Equiv witness.largeAction).symm position)).trans
        (witness.largeSupport position).symm
  smallSupport := by
    intro position
    rw [normalizedBranch,
      totalColoring_transport_selected_blockZero]
    exact (realization.smallSupport
      ((physicalK15Equiv witness.smallAction).symm position)).trans
        (witness.smallSupport position).symm
  freeLarge := by
    intro freeIndex largeIndex
    rw [normalizedBranch, totalColoring_transport_free_blockOne,
      witness.largePhysical, Equiv.symm_apply_apply,
      realization.freeLarge, freeChoiceNormalizer_label]
    simp [LargeFactorChoice.label]
  freeSmall := by
    intro freeIndex smallIndex
    rw [normalizedBranch, totalColoring_transport_free_blockZero,
      witness.smallPhysical, Equiv.symm_apply_apply,
      realization.freeSmall, freeChoiceNormalizer_label]
    simp [SmallFactorChoice.label]
  largeSmall := by
    intro largeIndex smallIndex
    rw [normalizedBranch, totalColoring_transport_blockOne_blockZero,
      witness.largePhysical, witness.smallPhysical,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      realization.largeSmall]
    simp [LargeFactorChoice.label, SmallFactorChoice.label]

#print axioms degreeNineTailPerm_templateCanonical
#print axioms transportBranchByPhysicalK15
#print axioms totalColoring_transportBranchByPhysicalK15
#print axioms transportBranchByPhysicalAndFree
#print axioms totalColoring_transportBranchByPhysicalAndFree
#print axioms semantic_factorAssignmentRealization
#print axioms FactorAssignmentRealization.normalize

end ContinuationDegreeNineTwistedRoot1PhysicalSymmetry61
end R4333
