import PricingG.UUQSupportTransport
import R4333Lean.ProfileDUUUFourSupportPositionSymmetry61
import R4333Lean.ProfileDUUUDegreeTenSupportTransportUUU2P15

/-!
# Exact support-pair quotient at UUU/block two/position fifteen

This is the support-normalization entrance for the last four-support slot.
Both foreign blocks are untwisted `K15` templates.  Their exact own-colour
five-sets are classified by the checked colour-two support table and are
transported, by strong template automorphisms, to the three representatives
`s0`, `s1`, and `s4` used by the 372-leaf restored-matrix catalogue.

There is no SAT or refutation premise in this file.
-/

namespace R4333
namespace UUTP15SupportPair

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourSupportForeignSupports61
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUFourSupportPositionSymmetry61
open ProfileDUUUDegreeTenSupportOrbitsB2P15
open ProfileDDegreeTenMatrixLeafDataUUU2P15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition : Fin 16 := Fin.last 15

abbrev Branch :=
  PositionedFourSupport .uut 2 SelectedPosition

def semantic (branch : Branch) :
    ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension .uut :=
  branch.toSemantic

@[simp] theorem semantic_block (branch : Branch) :
    (semantic branch).block = 2 := rfl

@[simp] theorem semantic_position_val (branch : Branch) :
    (semantic branch).position.val = 15 := rfl

@[simp] theorem semantic_blockRootColor (branch : Branch) :
    blockRootColor (semantic branch).block = 3 := rfl

/-! ## Classification of the two exact foreign supports -/

theorem firstSupport_templateIndependent (branch : Branch) :
    IsColorIndependentSet (k15Template false) 2
      (firstForeignOwnSupport (semantic branch)) := by
  change IsColorIndependentSet (k15Template false) 2
    (foreignOwnSupport (semantic branch) 0)
  intro left hleft right hright hlr hcolor
  let ext := semantic branch
  let tail := ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hnotOwn := foreignOwnSupport_edge_ne_own ext 0 (by
      change (0 : Fin 3) ≠ 2
      decide) left hleft right hright hlr
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      tail 0 (by decide) left right hlr
  apply hnotOwn
  change tail.coloring (blockVertex 0 left.val)
      (blockVertex 0 right.val) = 3
  change tail.coloring (blockVertex 0 left.val)
      (blockVertex 0 right.val) =
    canonicalPalette 1 (k15Template false left right) at hedge
  rw [hedge, hcolor]
  decide

theorem secondSupport_templateIndependent (branch : Branch) :
    IsColorIndependentSet (k15Template false) 2
      (secondForeignOwnSupport (semantic branch)) := by
  change IsColorIndependentSet (k15Template false) 2
    (foreignOwnSupport (semantic branch) 1)
  intro left hleft right hright hlr hcolor
  let ext := semantic branch
  let tail := ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hnotOwn := foreignOwnSupport_edge_ne_own ext 1 (by
      change (1 : Fin 3) ≠ 2
      decide) left hleft right hright hlr
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      tail 1 (by decide) left right hlr
  apply hnotOwn
  change tail.coloring (blockVertex 1 left.val)
      (blockVertex 1 right.val) = 3
  change tail.coloring (blockVertex 1 left.val)
      (blockVertex 1 right.val) =
    canonicalPalette 2 (k15Template false left right) at hedge
  rw [hedge, hcolor]
  decide

theorem exists_firstSupportIndex (branch : Branch) :
    ∃ i : Fin 11,
      firstForeignOwnSupport (semantic branch) = q2Support i := by
  have hmem : firstForeignOwnSupport (semantic branch) ∈
      CriticalK15PartitionClassification.independentFiveSets false 2 :=
    (CriticalK15PartitionClassification.mem_independentFiveSets_iff
      false 2 (firstForeignOwnSupport (semantic branch))).2
      ⟨firstForeignOwnSupport_card_eq_five (semantic branch),
        firstSupport_templateIndependent branch⟩
  rw [q2SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

theorem exists_secondSupportIndex (branch : Branch) :
    ∃ i : Fin 11,
      secondForeignOwnSupport (semantic branch) = q2Support i := by
  have hmem : secondForeignOwnSupport (semantic branch) ∈
      CriticalK15PartitionClassification.independentFiveSets false 2 :=
    (CriticalK15PartitionClassification.mem_independentFiveSets_iff
      false 2 (secondForeignOwnSupport (semantic branch))).2
      ⟨secondForeignOwnSupport_card_eq_five (semantic branch),
        secondSupport_templateIndependent branch⟩
  rw [q2SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

/-! ## Strong support normalization while fixing the selected endpoint -/

noncomputable def normalizeSupports (branch : Branch)
    (firstIndex secondIndex : Fin 11) : Branch where
  toDegreeFlooredFiveExtension :=
    transportDegreeFlooredFiveByTailPerm
      branch.toDegreeFlooredFiveExtension
      (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
        firstIndex secondIndex)
      (PricingG.UUQSupportTransport.uuq_supportNormalizer_templateCanonical (by rfl) (by rfl)
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
        firstIndex secondIndex)
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
        firstIndex secondIndex (blockVertex 2 SelectedPosition.val)) = 3
    rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockTwo]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
        firstIndex secondIndex (blockVertex 2 SelectedPosition.val)) ≠ 3
    rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockTwo]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
          firstIndex secondIndex))
      3 (blockVertex 2 SelectedPosition.val) = 10
    rw [colorDegree_relabelVertices,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockTwo]
    exact branch.tailOwnDegreeEqTen

@[simp] theorem normalizeSupports_rows (branch : Branch)
    (firstIndex secondIndex : Fin 11)
    (row : Fin 5) (x : ProfileDRowExtension.TailVertex) :
    (normalizeSupports branch firstIndex secondIndex).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
          firstIndex secondIndex x) := by
  rfl

private theorem q2SupportEquiv_image (index : Fin 11) :
    (q2Support index).image (q2SupportEquiv index) =
      q2Support (q2SupportRepresentative index) := by
  calc
    (q2Support index).image (q2SupportEquiv index) =
        (q2Support index).image (q2SupportMap index) := by
      apply Finset.image_congr
      intro q hq
      exact q2SupportEquiv_apply index q
    _ = q2Support (q2SupportRepresentative index) :=
      q2SupportMap_image index

theorem normalizeSupports_firstSupport
    (branch : Branch) (firstIndex secondIndex : Fin 11)
    (hsource : firstForeignOwnSupport (semantic branch) =
      q2Support firstIndex) :
    firstForeignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) =
      (support
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.normalizedSupportRepresentative
          firstIndex)).positions := by
  rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.normalizedSupportRepresentative_positions]
  change foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 0 = _
  change foreignOwnSupport (semantic branch) 0 = _ at hsource
  apply Finset.ext
  intro (p : Fin 15)
  have hsourceMem (q : Fin 15) :
      q ∈ foreignOwnSupport (semantic branch) 0 ↔
        q ∈ q2Support firstIndex := by
    rw [hsource]
    rfl
  constructor
  · intro hp
    have hpre : (q2SupportEquiv firstIndex).symm p ∈
        foreignOwnSupport (semantic branch) 0 := by
      apply (mem_foreignOwnSupport (semantic branch) 0 _).mpr
      have hpcolor := (mem_foreignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) 0 p).mp hp
      change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
            firstIndex secondIndex (blockVertex 2 SelectedPosition.val))
          (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
            firstIndex secondIndex (blockVertex 0 p.val)) = 3 at hpcolor
      rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockTwo,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockZero]
        at hpcolor
      exact hpcolor
    have hpImage : p ∈
        (q2Support firstIndex).image (q2SupportEquiv firstIndex) :=
      Finset.mem_image.mpr ⟨(q2SupportEquiv firstIndex).symm p,
        (hsourceMem _).mp hpre,
        (q2SupportEquiv firstIndex).apply_symm_apply p⟩
    rw [q2SupportEquiv_image] at hpImage
    exact hpImage
  · intro hp
    have hpImage : p ∈
        (q2Support firstIndex).image (q2SupportEquiv firstIndex) := by
      rw [q2SupportEquiv_image]
      exact hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    apply (mem_foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 0 p).mpr
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
          firstIndex secondIndex (blockVertex 2 SelectedPosition.val))
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
          firstIndex secondIndex (blockVertex 0 p.val)) = 3
    rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockZero]
    have hsymm : (q2SupportEquiv firstIndex).symm p = q := by
      apply (q2SupportEquiv firstIndex).injective
      simpa using hqp.symm
    rw [hsymm]
    exact (mem_foreignOwnSupport (semantic branch) 0 q).mp
      ((hsourceMem q).mpr hq)

theorem normalizeSupports_secondSupport
    (branch : Branch) (firstIndex secondIndex : Fin 11)
    (hsource : secondForeignOwnSupport (semantic branch) =
      q2Support secondIndex) :
    secondForeignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) =
      (support
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.normalizedSupportRepresentative
          secondIndex)).positions := by
  rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.normalizedSupportRepresentative_positions]
  change foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 1 = _
  change foreignOwnSupport (semantic branch) 1 = _ at hsource
  apply Finset.ext
  intro (p : Fin 15)
  have hsourceMem (q : Fin 15) :
      q ∈ foreignOwnSupport (semantic branch) 1 ↔
        q ∈ q2Support secondIndex := by
    rw [hsource]
    rfl
  constructor
  · intro hp
    have hpre : (q2SupportEquiv secondIndex).symm p ∈
        foreignOwnSupport (semantic branch) 1 := by
      apply (mem_foreignOwnSupport (semantic branch) 1 _).mpr
      have hpcolor := (mem_foreignOwnSupport
        (semantic (normalizeSupports branch firstIndex secondIndex)) 1 p).mp hp
      change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
            firstIndex secondIndex (blockVertex 2 SelectedPosition.val))
          (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
            firstIndex secondIndex (blockVertex 1 p.val)) = 3 at hpcolor
      rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockTwo,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockOne]
        at hpcolor
      exact hpcolor
    have hpImage : p ∈
        (q2Support secondIndex).image (q2SupportEquiv secondIndex) :=
      Finset.mem_image.mpr ⟨(q2SupportEquiv secondIndex).symm p,
        (hsourceMem _).mp hpre,
        (q2SupportEquiv secondIndex).apply_symm_apply p⟩
    rw [q2SupportEquiv_image] at hpImage
    exact hpImage
  · intro hp
    have hpImage : p ∈
        (q2Support secondIndex).image (q2SupportEquiv secondIndex) := by
      rw [q2SupportEquiv_image]
      exact hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    apply (mem_foreignOwnSupport
      (semantic (normalizeSupports branch firstIndex secondIndex)) 1 p).mpr
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
          firstIndex secondIndex (blockVertex 2 SelectedPosition.val))
        (ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm
          firstIndex secondIndex (blockVertex 1 p.val)) = 3
    rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.supportNormalizerTailPerm_blockOne]
    have hsymm : (q2SupportEquiv secondIndex).symm p = q := by
      apply (q2SupportEquiv secondIndex).injective
      simpa using hqp.symm
    rw [hsymm]
    exact (mem_foreignOwnSupport (semantic branch) 1 q).mp
      ((hsourceMem q).mpr hq)

structure NormalizedSupportPair where
  first : SupportRepresentative
  second : SupportRepresentative
  branch : Branch
  firstSupport :
    firstForeignOwnSupport (semantic branch) = (support first).positions
  secondSupport :
    secondForeignOwnSupport (semantic branch) = (support second).positions

/-- Every exact block-two/position-fifteen four-support object enters one of
the nine ordered support pairs used by the full restored-matrix catalogue. -/
theorem exists_normalizedSupportPair (branch : Branch) :
    Nonempty NormalizedSupportPair := by
  obtain ⟨firstIndex, hfirst⟩ := exists_firstSupportIndex branch
  obtain ⟨secondIndex, hsecond⟩ := exists_secondSupportIndex branch
  exact ⟨{
    first :=
      ProfileDUUUDegreeTenSupportTransportUUU2P15.normalizedSupportRepresentative
        firstIndex
    second :=
      ProfileDUUUDegreeTenSupportTransportUUU2P15.normalizedSupportRepresentative
        secondIndex
    branch := normalizeSupports branch firstIndex secondIndex
    firstSupport := normalizeSupports_firstSupport branch firstIndex
      secondIndex hfirst
    secondSupport := normalizeSupports_secondSupport branch firstIndex
      secondIndex hsecond
  }⟩

#print axioms firstSupport_templateIndependent
#print axioms secondSupport_templateIndependent
#print axioms exists_firstSupportIndex
#print axioms exists_secondSupportIndex
#print axioms normalizeSupports_firstSupport
#print axioms normalizeSupports_secondSupport
#print axioms exists_normalizedSupportPair

end UUTP15SupportPair
end R4333
