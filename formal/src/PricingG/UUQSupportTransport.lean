import R4333Lean.ProfileDUUUDegreeTenSupportTransportUUU2P15

namespace PricingG.UUQSupportTransport
open R4333
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61 ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF ProfileDUUUDegreeTenSupportOrbits61
open ProfileDUUUDegreeTenSupportOrbitsB2P15
open ProfileDDegreeTenMatrixLeafDataUUU2P15 ProfileDDegreeTenMatrixTransport61
open ProfileDUUUDegreeTenSupportClassificationUUU2P15
open ProfileDUUUDegreeTenSupportTransportUUU2P15
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem uuq_supportNormalizer_templateCanonical
    {kind : ProfileDTripleJoinReduction.Kind}
    (hzero : kind.twisted 0 = false) (hone : kind.twisted 1 = false)
    (tail : ProfileDTripleJoinReduction.Witness kind)
    (firstIndex secondIndex : Fin 11) :
    ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex target left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex target right)) =
        SingleRootStarCNF.canonicalPalette (Fin.succ target)
          (SingleRootStarCNF.templateColor (blockSize target)
            (Kind.twisted kind target) left right) := by
  intro target left right hleft hright hlr
  fin_cases target
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 0 left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 0 right)) =
        SingleRootStarCNF.canonicalPalette 1
          (SingleRootStarCNF.templateColor 15 (kind.twisted 0) left right)
    rw [hzero]
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 0 left =
        ProfileDTripleJoinReduction.blockVertex 0 leftFin.val by rfl,
      supportNormalizerTailPerm_blockZero,
      show ProfileDTripleJoinReduction.blockVertex 0 right =
        ProfileDTripleJoinReduction.blockVertex 0 rightFin.val by rfl,
      supportNormalizerTailPerm_blockZero]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 0 (by decide)
          ((q2SupportEquiv firstIndex).symm leftFin)
          ((q2SupportEquiv firstIndex).symm rightFin)
          ((q2SupportEquiv firstIndex).symm.injective.ne hne)
    have htwisted : kind.twisted (0 : Fin 3) = false := hzero
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 0
            ((q2SupportEquiv firstIndex).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 0
            ((q2SupportEquiv firstIndex).symm rightFin).val) =
          SingleRootStarCNF.canonicalPalette 1
            (k15Template false
              ((q2SupportEquiv firstIndex).symm leftFin)
              ((q2SupportEquiv firstIndex).symm rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 1
            (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 1)
          (q2SupportEquiv_symm_preserves firstIndex leftFin rightFin hne)
      _ = _ := by
        simp [blockSize, SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 1 left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 1 right)) =
        SingleRootStarCNF.canonicalPalette 2
          (SingleRootStarCNF.templateColor 15 (kind.twisted 1) left right)
    rw [hone]
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 1 left =
        ProfileDTripleJoinReduction.blockVertex 1 leftFin.val by rfl,
      supportNormalizerTailPerm_blockOne,
      show ProfileDTripleJoinReduction.blockVertex 1 right =
        ProfileDTripleJoinReduction.blockVertex 1 rightFin.val by rfl,
      supportNormalizerTailPerm_blockOne]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 1 (by decide)
          ((q2SupportEquiv secondIndex).symm leftFin)
          ((q2SupportEquiv secondIndex).symm rightFin)
          ((q2SupportEquiv secondIndex).symm.injective.ne hne)
    have htwisted : kind.twisted (1 : Fin 3) = false := hone
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1
            ((q2SupportEquiv secondIndex).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 1
            ((q2SupportEquiv secondIndex).symm rightFin).val) =
          SingleRootStarCNF.canonicalPalette 2
            (k15Template false
              ((q2SupportEquiv secondIndex).symm leftFin)
              ((q2SupportEquiv secondIndex).symm rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 2
            (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 2)
          (q2SupportEquiv_symm_preserves secondIndex leftFin rightFin hne)
      _ = _ := by
        simp [blockSize, SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 16 at hleft
    change right < 16 at hright
    change
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 2 left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 2 right)) =
        SingleRootStarCNF.canonicalPalette 3
          (SingleRootStarCNF.templateColor 16 (kind.twisted 2) left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 2 left =
        ProfileDTripleJoinReduction.blockVertex 2 leftFin.val by rfl,
      supportNormalizerTailPerm_blockTwo,
      show ProfileDTripleJoinReduction.blockVertex 2 right =
        ProfileDTripleJoinReduction.blockVertex 2 rightFin.val by rfl,
      supportNormalizerTailPerm_blockTwo]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        tail 2 (by decide) leftFin rightFin hne
    simpa [SingleRootStarCNF.templateColor, SingleRootStarCNF.fin16,
      leftFin, rightFin, Nat.mod_eq_of_lt hleft,
      Nat.mod_eq_of_lt hright] using hedge

noncomputable def normalizeUUQExactDegreeTenSupports
    {kind : ProfileDTripleJoinReduction.Kind}
    (hzero : kind.twisted 0 = false) (hone : kind.twisted 1 = false)
    {sourceCoordinates : MatrixCoordinates 2}
    {sourceMatrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch kind 2 ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition
      sourceCoordinates sourceMatrix)
    (firstIndex secondIndex : Fin 11)
    (hfirst : sourceCoordinates.first.positions = q2Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = q2Support secondIndex) :
    ExactDegreeTenMatrixBranch kind 2 ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition
      (coordinatesFor (normalizedSupportRepresentative firstIndex)
        (normalizedSupportRepresentative secondIndex))
      (supportNormalizedMatrix sourceCoordinates sourceMatrix firstIndex
        secondIndex hfirst hsecond) :=
  transportExactDegreeTenMatrixBranch exact
    (supportNormalizerTailPerm firstIndex secondIndex)
    (uuq_supportNormalizer_templateCanonical hzero hone
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      firstIndex secondIndex)
    (by rw [supportNormalizerTailPerm_blockTwo])
    (q2SupportEquiv firstIndex).symm
    (q2SupportEquiv secondIndex).symm
    (supportNormalizationMatrixPerm sourceCoordinates firstIndex secondIndex
      hfirst hsecond)
    (supportNormalizerTailPerm_blockZero firstIndex secondIndex)
    (supportNormalizerTailPerm_blockOne firstIndex secondIndex)
    (firstNormalizer_positions firstIndex hfirst)
    (secondNormalizer_positions secondIndex hsecond)
    (supportNormalization_coordinates_covariant sourceCoordinates firstIndex
      secondIndex hfirst hsecond)
    (ProfileDUUUDegreeTenEndToEndSemanticUUU0P2.matrixBlockPerm_preserves_cross_group _ _ _)
    (by intro left right _; rfl)

#print axioms uuq_supportNormalizer_templateCanonical
#print axioms normalizeUUQExactDegreeTenSupports
end PricingG.UUQSupportTransport
