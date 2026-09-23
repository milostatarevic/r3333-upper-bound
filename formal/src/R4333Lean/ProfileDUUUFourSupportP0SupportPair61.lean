import R4333Lean.ProfileDUUUFourSupportPositionSymmetry61
import R4333Lean.ProfileDUUUDegreeTenEndToEndSemantic61

/-!
# Exact support-pair quotient at UUU/block zero/position zero

This is the semantic entrance used by the restored-`K15` four-support
quotient.  It contains no SAT result.  Starting from an arbitrary exact
four-support branch at block zero and position zero, it

* identifies the two foreign supports in the complete checked `U15` and
  `U16` independent-five-set tables;
* transports the whole five-row extension by the explicit strong template
  automorphisms from those tables; and
* proves that the transported supports are exactly one of `U15` supports
  `0`, `2`, `7` and `U16` support `0`.

The selected endpoint is fixed by this transport, so all four own-colour
row incidences, the fifth-row exclusion, the exact tail degree ten, and all
degree floors are preserved definitionally or by equivariance.
-/

namespace R4333
namespace ProfileDUUUFourSupportP0SupportPair61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourSupportForeignSupports61
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUFourSupportPositionSymmetry61
open ProfileDUUUDegreeTenSupportOrbits61
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenEndToEndSemantic61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition : Fin 15 := 0

abbrev Branch :=
  PositionedFourSupport .uuu 0 SelectedPosition

def semantic (branch : Branch) :
    ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension .uuu :=
  branch.toSemantic

@[simp] theorem semantic_block (branch : Branch) :
    (semantic branch).block = 0 := rfl

@[simp] theorem semantic_position_val (branch : Branch) :
    (semantic branch).position.val = 0 := rfl

@[simp] theorem semantic_blockRootColor (branch : Branch) :
    blockRootColor (semantic branch).block = 1 := rfl

/-! ## Classification of the two exact foreign supports -/

theorem firstSupport_templateIndependent (branch : Branch) :
    IsColorIndependentSet (k15Template false) 1
      (firstForeignOwnSupport (semantic branch)) := by
  change IsColorIndependentSet (k15Template false) 1
    (foreignOwnSupport (semantic branch) 1)
  intro left hleft right hright hlr hcolor
  let ext := semantic branch
  let tail := ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hnotOwn := foreignOwnSupport_edge_ne_own ext 1 (by
      change (1 : Fin 3) ≠ 0
      decide) left hleft right hright hlr
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      tail 1 (by decide) left right hlr
  apply hnotOwn
  change tail.coloring (blockVertex 1 left.val)
      (blockVertex 1 right.val) = 1
  change tail.coloring (blockVertex 1 left.val)
      (blockVertex 1 right.val) =
    canonicalPalette 2 (k15Template false left right) at hedge
  rw [hedge, hcolor]
  decide

theorem secondSupport_templateIndependent (branch : Branch) :
    IsColorIndependentSet (k16Template false) 1
      (secondForeignOwnSupport (semantic branch)) := by
  change IsColorIndependentSet (k16Template false) 1
    (foreignOwnSupport (semantic branch) 2)
  intro left hleft right hright hlr hcolor
  let ext := semantic branch
  let tail := ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hnotOwn := foreignOwnSupport_edge_ne_own ext 2 (by
      change (2 : Fin 3) ≠ 0
      decide) left hleft right hright hlr
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
      tail 2 (by decide) left right hlr
  apply hnotOwn
  change tail.coloring (blockVertex 2 left.val)
      (blockVertex 2 right.val) = 1
  change tail.coloring (blockVertex 2 left.val)
      (blockVertex 2 right.val) =
    canonicalPalette 3 (k16Template false left right) at hedge
  rw [hedge, hcolor]
  decide

theorem exists_firstSupportIndex (branch : Branch) :
    ∃ i : Fin 11,
      firstForeignOwnSupport (semantic branch) = u15Support i := by
  have hmem : firstForeignOwnSupport (semantic branch) ∈
      CriticalK15PartitionClassification.independentFiveSets false 1 :=
    (CriticalK15PartitionClassification.mem_independentFiveSets_iff
      false 1 (firstForeignOwnSupport (semantic branch))).2
      ⟨firstForeignOwnSupport_card_eq_five (semantic branch),
        firstSupport_templateIndependent branch⟩
  rw [u15SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

theorem exists_secondSupportIndex (branch : Branch) :
    ∃ i : Fin 16,
      secondForeignOwnSupport (semantic branch) = u16Support i := by
  have hmem : secondForeignOwnSupport (semantic branch) ∈
      u16IndependentFiveSets := by
    unfold u16IndependentFiveSets
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _,
          secondForeignOwnSupport_card_eq_five (semantic branch)⟩
    · exact (colorViolationCount_eq_zero_iff _ _ _).2
        (secondSupport_templateIndependent branch)
  rw [u16SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

/-! ## Strong support normalization while fixing the selected endpoint -/

noncomputable def normalizeSupports (branch : Branch)
    (firstIndex : Fin 11) (secondIndex : Fin 16) : Branch where
  toDegreeFlooredFiveExtension :=
    transportDegreeFlooredFiveByTailPerm
      branch.toDegreeFlooredFiveExtension
      (supportNormalizerTailPerm firstIndex secondIndex)
      (supportNormalizer_templateCanonical
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
        firstIndex secondIndex)
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      (supportNormalizerTailPerm firstIndex secondIndex
        (blockVertex 0 SelectedPosition.val)) = 1
    rw [supportNormalizerTailPerm_blockZero]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      (supportNormalizerTailPerm firstIndex secondIndex
        (blockVertex 0 SelectedPosition.val)) ≠ 1
    rw [supportNormalizerTailPerm_blockZero]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (supportNormalizerTailPerm firstIndex secondIndex))
      1 (blockVertex 0 SelectedPosition.val) = 10
    rw [colorDegree_relabelVertices,
      supportNormalizerTailPerm_blockZero]
    exact branch.tailOwnDegreeEqTen

@[simp] theorem normalizeSupports_rows (branch : Branch)
    (firstIndex : Fin 11) (secondIndex : Fin 16)
    (row : Fin 5) (x : ProfileDRowExtension.TailVertex) :
    (normalizeSupports branch firstIndex secondIndex).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (supportNormalizerTailPerm firstIndex secondIndex x) := by
  rfl

theorem normalizeSupports_firstSupport
    (branch : Branch) (firstIndex : Fin 11) (secondIndex : Fin 16)
    (hsource : firstForeignOwnSupport (semantic branch) =
      u15Support firstIndex) :
    firstForeignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) =
      u15Support (u15SupportRepresentative firstIndex) := by
  change foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 1 = _
  change foreignOwnSupport (semantic branch) 1 = _ at hsource
  apply Finset.ext
  intro (p : Fin 15)
  have hsourceMem (q : Fin 15) :
      q ∈ foreignOwnSupport (semantic branch) 1 ↔
        q ∈ u15Support firstIndex := by
    rw [hsource]
    rfl
  have himage :
      (u15Support firstIndex).image (u15SupportEquiv firstIndex) =
        u15Support (u15SupportRepresentative firstIndex) := by
    calc
      (u15Support firstIndex).image (u15SupportEquiv firstIndex) =
          (u15Support firstIndex).image (u15SupportMap firstIndex) := by
        apply Finset.image_congr
        intro q hq
        exact u15SupportEquiv_apply firstIndex q
      _ = u15Support (u15SupportRepresentative firstIndex) :=
        u15SupportMap_image firstIndex
  constructor
  · intro hp
    have hpre : (u15SupportEquiv firstIndex).symm p ∈
        foreignOwnSupport (semantic branch) 1 := by
      apply (mem_foreignOwnSupport (semantic branch) 1 _).mpr
      have hpcolor := (mem_foreignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) 1 p).mp hp
      change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (blockVertex 0 SelectedPosition.val))
          (supportNormalizerTailPerm firstIndex secondIndex
            (blockVertex 1 p.val)) = 1 at hpcolor
      rw [supportNormalizerTailPerm_blockZero,
        supportNormalizerTailPerm_blockOne] at hpcolor
      exact hpcolor
    have hpImage : p ∈
        (u15Support firstIndex).image (u15SupportEquiv firstIndex) :=
      Finset.mem_image.mpr ⟨(u15SupportEquiv firstIndex).symm p,
        (hsourceMem _).mp hpre,
        (u15SupportEquiv firstIndex).apply_symm_apply p⟩
    rw [himage] at hpImage
    exact hpImage
  · intro hp
    have hpImage : p ∈
        (u15Support firstIndex).image (u15SupportEquiv firstIndex) := by
      rw [himage]
      exact hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    apply (mem_foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 1 p).mpr
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (supportNormalizerTailPerm firstIndex secondIndex
          (blockVertex 0 SelectedPosition.val))
        (supportNormalizerTailPerm firstIndex secondIndex
          (blockVertex 1 p.val)) = 1
    rw [supportNormalizerTailPerm_blockZero,
      supportNormalizerTailPerm_blockOne]
    have hsymm : (u15SupportEquiv firstIndex).symm p = q := by
      apply (u15SupportEquiv firstIndex).injective
      simpa using hqp.symm
    rw [hsymm]
    exact (mem_foreignOwnSupport (semantic branch) 1 q).mp
      ((hsourceMem q).mpr hq)

theorem normalizeSupports_secondSupport
    (branch : Branch) (firstIndex : Fin 11) (secondIndex : Fin 16)
    (hsource : secondForeignOwnSupport (semantic branch) =
      u16Support secondIndex) :
    secondForeignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) =
      u16Support 0 := by
  change foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 2 = _
  change foreignOwnSupport (semantic branch) 2 = _ at hsource
  apply Finset.ext
  intro (p : Fin 16)
  have hsourceMem (q : Fin 16) :
      q ∈ foreignOwnSupport (semantic branch) 2 ↔
        q ∈ u16Support secondIndex := by
    rw [hsource]
    rfl
  have himage :
      (u16Support secondIndex).image (u16SupportEquiv secondIndex) =
        u16Support 0 := by
    calc
      (u16Support secondIndex).image (u16SupportEquiv secondIndex) =
          (u16Support secondIndex).image (u16SupportMap secondIndex) := by
        apply Finset.image_congr
        intro q hq
        exact u16SupportEquiv_apply secondIndex q
      _ = u16Support 0 := u16SupportMap_image secondIndex
  constructor
  · intro hp
    have hpre : (u16SupportEquiv secondIndex).symm p ∈
        foreignOwnSupport (semantic branch) 2 := by
      apply (mem_foreignOwnSupport (semantic branch) 2 _).mpr
      have hpcolor := (mem_foreignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) 2 p).mp hp
      change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (blockVertex 0 SelectedPosition.val))
          (supportNormalizerTailPerm firstIndex secondIndex
            (blockVertex 2 p.val)) = 1 at hpcolor
      rw [supportNormalizerTailPerm_blockZero,
        supportNormalizerTailPerm_blockTwo] at hpcolor
      exact hpcolor
    have hpImage : p ∈
        (u16Support secondIndex).image (u16SupportEquiv secondIndex) :=
      Finset.mem_image.mpr ⟨(u16SupportEquiv secondIndex).symm p,
        (hsourceMem _).mp hpre,
        (u16SupportEquiv secondIndex).apply_symm_apply p⟩
    rw [himage] at hpImage
    exact hpImage
  · intro hp
    have hpImage : p ∈
        (u16Support secondIndex).image (u16SupportEquiv secondIndex) := by
      rw [himage]
      exact hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    apply (mem_foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 2 p).mpr
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (supportNormalizerTailPerm firstIndex secondIndex
          (blockVertex 0 SelectedPosition.val))
        (supportNormalizerTailPerm firstIndex secondIndex
          (blockVertex 2 p.val)) = 1
    rw [supportNormalizerTailPerm_blockZero,
      supportNormalizerTailPerm_blockTwo]
    have hsymm : (u16SupportEquiv secondIndex).symm p = q := by
      apply (u16SupportEquiv secondIndex).injective
      simpa using hqp.symm
    rw [hsymm]
    exact (mem_foreignOwnSupport (semantic branch) 2 q).mp
      ((hsourceMem q).mpr hq)

structure NormalizedSupportPair where
  kind : SupportKind
  branch : Branch
  firstSupport :
    firstForeignOwnSupport (semantic branch) =
      u15Support (supportIndex kind)
  secondSupport :
    secondForeignOwnSupport (semantic branch) = u16Support 0

/-- Every exact block-zero/position-zero four-support object enters one of
the three support-pair selectors used by the authoritative quotient CNF. -/
theorem exists_normalizedSupportPair (branch : Branch) :
    Nonempty NormalizedSupportPair := by
  obtain ⟨firstIndex, hfirst⟩ := exists_firstSupportIndex branch
  obtain ⟨secondIndex, hsecond⟩ := exists_secondSupportIndex branch
  let kind := normalizedSupportKind firstIndex
  refine ⟨{
    kind := kind
    branch := normalizeSupports branch firstIndex secondIndex
    firstSupport := ?_
    secondSupport := normalizeSupports_secondSupport branch firstIndex
      secondIndex hsecond
  }⟩
  rw [supportIndex_normalizedSupportKind]
  exact normalizeSupports_firstSupport branch firstIndex secondIndex hfirst

#print axioms firstSupport_templateIndependent
#print axioms secondSupport_templateIndependent
#print axioms exists_firstSupportIndex
#print axioms exists_secondSupportIndex
#print axioms normalizeSupports_firstSupport
#print axioms normalizeSupports_secondSupport
#print axioms exists_normalizedSupportPair

end ProfileDUUUFourSupportP0SupportPair61
end R4333
