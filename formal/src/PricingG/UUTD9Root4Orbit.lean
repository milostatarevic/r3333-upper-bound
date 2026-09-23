import PricingG.UUTD9Root4Physical

/-! Continuation-authored (locks/duuu), 2026-08-05.
Twisted case (slot 3, root 4) factor-orbit-coverage clone of
ProfileDUUUDegreeNineFactorOrbitCoverage61.  The physical support-order
tables are case-independent (verbatim); the compatible-permutation
catalogues and normalizer words are regenerated from
twisted_root4_orbits.json data (label-side k15Template sites flipped
false -> true; physical colorings renamed to the twistedRoot4 names).
STRUCTURAL EDIT (unique in the family): the root-4 label stabilizer is
TRIVIAL, so the rooted normal-template involution layer of the archive
module (root normalizer words, root normalizer equations, the root
physical-normalization witness, and the flipped branch of the reduction)
is removed entirely.  The diagonal quotient keeps all `11 x 12 = 132`
independent-physical representatives, and the coverage statement is the
direct product enumeration with no involution disjunct.  Because there is
no RootStabilizer module for root 4, the explicit label-order tables and
their `orderEmbOfFin` characterizations (previously provided by that
module) are inlined here.  The archive's identity free representative is
not compatible with the twisted root-4 template; the first compatible
free permutation `(0 2 1 3 4)` (the swap of positions 1 and 2) is used
instead, verified by kernel reduction. -/

/-!
# Exact factor-catalogue orbit coverage in the twisted root-4 case

This module internalizes the finite part of the symmetry quotient.  The raw
factor catalogues have `10`, `110`, and `120` entries.  Independent physical
symmetries reduce the latter two to `11` and `12` representatives.  The
root-4 normal-template stabilizer is trivial, so no further diagonal
halving occurs: the quotient keeps all `132` representative pairs.

Every table below is checked against the semantic choice structures by Lean
kernel reduction; no external orbit computation is trusted.
-/

namespace R4333
namespace UUTD9Root4Orbit

open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open UUTD9Root4Case
open UUTD9Root4CNF
open UUTD9Root4Factor
open UUTD9Root4Physical
open ProfileDDegreeTenMatrixCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex

/-! ## Explicit label orders (inlined; no RootStabilizer module for root 4) -/

def explicitFreeLabelOrder : Fin 5 → Fin 15 := ![5, 8, 11, 12, 14]
def explicitLargeLabelOrder : Fin 5 → Fin 15 := ![0, 1, 2, 10, 13]
def explicitSmallLabelOrder : Fin 4 → Fin 15 := ![3, 6, 7, 9]

private theorem explicitFreeLabelOrder_mem (position : Fin 5) :
    explicitFreeLabelOrder position ∈ twistedRoot4FreeLabelSet := by
  fin_cases position <;> decide

private theorem explicitLargeLabelOrder_mem (position : Fin 5) :
    explicitLargeLabelOrder position ∈ twistedRoot4LargeLabelSet := by
  fin_cases position <;> decide

private theorem explicitSmallLabelOrder_mem (position : Fin 4) :
    explicitSmallLabelOrder position ∈ twistedRoot4SmallLabelSet := by
  fin_cases position <;> decide

private theorem explicitFreeLabelOrder_strictMono :
    StrictMono explicitFreeLabelOrder := by decide

private theorem explicitLargeLabelOrder_strictMono :
    StrictMono explicitLargeLabelOrder := by decide

private theorem explicitSmallLabelOrder_strictMono :
    StrictMono explicitSmallLabelOrder := by decide

theorem explicitFreeLabelOrder_eq (position : Fin 5) :
    explicitFreeLabelOrder position = (freeLabelOrder position).1 := by
  have hfun : explicitFreeLabelOrder =
      twistedRoot4FreeLabelSet.orderEmbOfFin twistedRoot4FreeLabelSet_card :=
    Finset.orderEmbOfFin_unique twistedRoot4FreeLabelSet_card
      explicitFreeLabelOrder_mem explicitFreeLabelOrder_strictMono
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

theorem explicitLargeLabelOrder_eq (position : Fin 5) :
    explicitLargeLabelOrder position = (largeLabelOrder position).1 := by
  have hfun : explicitLargeLabelOrder =
      twistedRoot4LargeLabelSet.orderEmbOfFin twistedRoot4LargeLabelSet_card :=
    Finset.orderEmbOfFin_unique twistedRoot4LargeLabelSet_card
      explicitLargeLabelOrder_mem explicitLargeLabelOrder_strictMono
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

theorem explicitSmallLabelOrder_eq (position : Fin 4) :
    explicitSmallLabelOrder position = (smallLabelOrder position).1 := by
  have hfun : explicitSmallLabelOrder =
      twistedRoot4SmallLabelSet.orderEmbOfFin twistedRoot4SmallLabelSet_card :=
    Finset.orderEmbOfFin_unique twistedRoot4SmallLabelSet_card
      explicitSmallLabelOrder_mem explicitSmallLabelOrder_strictMono
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

/-! ## Fully explicit support orders and permutation enumerations -/

def explicitLargeSupportOrder : Fin 11 → Fin 5 → Fin 15 :=
  ![![0, 1, 2, 10, 13], ![0, 1, 3, 11, 12],
    ![0, 7, 8, 10, 11], ![1, 2, 3, 9, 14],
    ![1, 6, 9, 10, 11], ![1, 6, 12, 13, 14],
    ![2, 5, 8, 9, 10], ![3, 4, 8, 9, 11],
    ![4, 5, 6, 9, 14], ![4, 6, 7, 11, 12],
    ![5, 6, 7, 10, 13]]

def explicitSmallSupportOrder : Fin 60 → Fin 4 → Fin 15 :=
  ![![0, 1, 2, 10], ![0, 1, 2, 13], ![0, 1, 3, 11],
    ![0, 1, 3, 12], ![0, 1, 10, 13], ![0, 1, 11, 12],
    ![0, 2, 3, 8], ![0, 2, 10, 13], ![0, 3, 11, 12],
    ![0, 7, 8, 10], ![0, 7, 8, 11], ![0, 7, 10, 11],
    ![0, 7, 12, 13], ![0, 8, 10, 11], ![1, 2, 3, 9],
    ![1, 2, 3, 14], ![1, 2, 9, 14], ![1, 2, 10, 13],
    ![1, 3, 9, 14], ![1, 3, 11, 12], ![1, 6, 9, 10],
    ![1, 6, 9, 11], ![1, 6, 10, 11], ![1, 6, 12, 13],
    ![1, 6, 12, 14], ![1, 6, 13, 14], ![1, 9, 10, 11],
    ![1, 12, 13, 14], ![2, 3, 9, 14], ![2, 5, 8, 9],
    ![2, 5, 8, 10], ![2, 5, 9, 10], ![2, 5, 13, 14],
    ![2, 8, 9, 10], ![3, 4, 8, 9], ![3, 4, 8, 11],
    ![3, 4, 9, 11], ![3, 4, 12, 14], ![3, 8, 9, 11],
    ![4, 5, 6, 9], ![4, 5, 6, 14], ![4, 5, 7, 8],
    ![4, 5, 9, 14], ![4, 6, 7, 11], ![4, 6, 7, 12],
    ![4, 6, 9, 14], ![4, 6, 11, 12], ![4, 7, 11, 12],
    ![4, 8, 9, 11], ![5, 6, 7, 10], ![5, 6, 7, 13],
    ![5, 6, 9, 14], ![5, 6, 10, 13], ![5, 7, 10, 13],
    ![5, 8, 9, 10], ![6, 7, 10, 13], ![6, 7, 11, 12],
    ![6, 9, 10, 11], ![6, 12, 13, 14], ![7, 8, 10, 11]]

private theorem explicitLargeSupportOrder_mem
    (support : Fin 11) (position : Fin 5) :
    explicitLargeSupportOrder support position ∈
      (indexedLargeSupport support).1 := by
  fin_cases support <;> fin_cases position <;> decide

private theorem explicitSmallSupportOrder_mem
    (support : Fin 60) (position : Fin 4) :
    explicitSmallSupportOrder support position ∈
      (indexedSmallSupport support).1 := by
  fin_cases support <;> fin_cases position <;> decide

private theorem explicitLargeSupportOrder_strictMono
    (support : Fin 11) : StrictMono (explicitLargeSupportOrder support) := by
  fin_cases support <;> decide

private theorem explicitSmallSupportOrder_strictMono
    (support : Fin 60) : StrictMono (explicitSmallSupportOrder support) := by
  fin_cases support <;> decide

theorem explicitLargeSupportOrder_eq
    (support : Fin 11) (position : Fin 5) :
    explicitLargeSupportOrder support position =
      (largeFactorOrder (indexedLargeSupport support) position).1 := by
  have hfun : explicitLargeSupportOrder support =
      (indexedLargeSupport support).1.orderEmbOfFin
        (largeFactorSupport_card (indexedLargeSupport support)) :=
    Finset.orderEmbOfFin_unique
      (largeFactorSupport_card (indexedLargeSupport support))
      (explicitLargeSupportOrder_mem support)
      (explicitLargeSupportOrder_strictMono support)
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

theorem explicitSmallSupportOrder_eq
    (support : Fin 60) (position : Fin 4) :
    explicitSmallSupportOrder support position =
      (smallFactorOrder (indexedSmallSupport support) position).1 := by
  have hfun : explicitSmallSupportOrder support =
      (indexedSmallSupport support).1.orderEmbOfFin
        (smallFactorSupport_card (indexedSmallSupport support)) :=
    Finset.orderEmbOfFin_unique
      (smallFactorSupport_card (indexedSmallSupport support))
      (explicitSmallSupportOrder_mem support)
      (explicitSmallSupportOrder_strictMono support)
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

theorem fiveVertexPermutations_length : fiveVertexPermutations.length = 120 := by
  decide

theorem fourVertexPermutations_length : fourVertexPermutations.length = 24 := by
  decide

def fivePermutationAt (index : Fin 120) : Equiv.Perm (Fin 5) :=
  fiveVertexPermutations.get
    ⟨index.val, by rw [fiveVertexPermutations_length]; exact index.isLt⟩

def fourPermutationAt (index : Fin 24) : Equiv.Perm (Fin 4) :=
  fourVertexPermutations.get
    ⟨index.val, by rw [fourVertexPermutations_length]; exact index.isLt⟩

noncomputable def fivePermutationIndex
    (perm : Equiv.Perm (Fin 5)) : Fin 120 :=
  ⟨fiveVertexPermutations.idxOf perm, by
    rw [← fiveVertexPermutations_length]
    exact List.idxOf_lt_length_of_mem (mem_fiveVertexPermutations perm)⟩

private theorem mem_fourVertexPermutations_orbit
    (perm : Equiv.Perm (Fin 4)) : perm ∈ fourVertexPermutations := by
  apply mem_permsOfList_of_mem
  intro position _
  fin_cases position <;> simp

noncomputable def fourPermutationIndex
    (perm : Equiv.Perm (Fin 4)) : Fin 24 :=
  ⟨fourVertexPermutations.idxOf perm, by
    rw [← fourVertexPermutations_length]
    exact List.idxOf_lt_length_of_mem
      (mem_fourVertexPermutations_orbit perm)⟩

theorem fivePermutationAt_index (perm : Equiv.Perm (Fin 5)) :
    fivePermutationAt (fivePermutationIndex perm) = perm := by
  apply List.getElem_idxOf

theorem fourPermutationAt_index (perm : Equiv.Perm (Fin 4)) :
    fourPermutationAt (fourPermutationIndex perm) = perm := by
  apply List.getElem_idxOf

/-! ## The exact 110- and 120-entry labelled catalogues -/

def largeCataloguePermIndex : Fin 110 → Fin 120 :=
  ![0, 16, 25, 45, 63, 66, 78, 89, 98, 107,
    1, 21, 24, 40, 61, 70, 77, 80, 103, 116,
    10, 14, 33, 47, 50, 59, 87, 90, 100, 108,
    15, 18, 31, 44, 48, 64, 82, 86, 99, 115,
    9, 23, 34, 38, 53, 56, 75, 91, 109, 118,
    15, 18, 31, 44, 48, 64, 82, 86, 99, 115,
    7, 20, 39, 42, 54, 65, 74, 83, 97, 117,
    15, 18, 31, 44, 48, 64, 82, 86, 99, 115,
    1, 21, 24, 40, 61, 70, 77, 80, 103, 116,
    15, 18, 31, 44, 48, 64, 82, 86, 99, 115,
    13, 22, 30, 41, 49, 69, 76, 84, 105, 119]

def smallCataloguePermIndex : Fin 120 → Fin 24 :=
  ![10, 14, 4, 12, 4, 12, 10, 14, 13, 22, 15, 18,
    0, 16, 1, 21, 0, 16, 7, 20, 1, 21, 5, 8,
    5, 8, 9, 23, 2, 11, 0, 16, 6, 17, 0, 16,
    7, 20, 1, 21, 1, 21, 7, 20, 2, 11, 2, 11,
    0, 16, 6, 17, 10, 14, 7, 20, 15, 18, 5, 8,
    6, 17, 0, 16, 7, 20, 15, 18, 2, 11, 0, 16,
    6, 17, 1, 21, 7, 20, 4, 12, 10, 14, 10, 14,
    15, 18, 2, 11, 0, 16, 0, 16, 6, 17, 7, 20,
    15, 18, 0, 16, 2, 11, 1, 21, 7, 20, 6, 17,
    7, 20, 13, 22, 15, 18, 9, 23, 15, 18, 10, 14]

def largeCatalogueSupportIndex (index : Fin 110) : Fin 11 :=
  ⟨index.val / 10, by omega⟩

def smallCatalogueSupportIndex (index : Fin 120) : Fin 60 :=
  ⟨index.val / 2, by omega⟩

def explicitLargePhysical
    (support : Fin 11) (perm : Fin 120) (position : Fin 5) : Fin 15 :=
  explicitLargeSupportOrder support (fivePermutationAt perm position)

def explicitSmallPhysical
    (support : Fin 60) (perm : Fin 24) (position : Fin 4) : Fin 15 :=
  explicitSmallSupportOrder support (fourPermutationAt perm position)

def largeCataloguePhysical (index : Fin 110) (position : Fin 5) : Fin 15 :=
  explicitLargePhysical (largeCatalogueSupportIndex index)
    (largeCataloguePermIndex index) position

def smallCataloguePhysical (index : Fin 120) (position : Fin 4) : Fin 15 :=
  explicitSmallPhysical (smallCatalogueSupportIndex index)
    (smallCataloguePermIndex index) position

def ExplicitLargeCompatible (support : Fin 11) (perm : Fin 120) : Prop :=
  ∀ left right : Fin 5, left ≠ right →
    k15Template true (explicitLargeLabelOrder left)
        (explicitLargeLabelOrder right) =
      twistedRoot4LargePhysicalColoring
        (explicitLargePhysical support perm left)
        (explicitLargePhysical support perm right)

def ExplicitSmallCompatible (support : Fin 60) (perm : Fin 24) : Prop :=
  ∀ left right : Fin 4, left ≠ right →
    k15Template true (explicitSmallLabelOrder left)
        (explicitSmallLabelOrder right) =
      twistedRoot4SmallPhysicalColoring
        (explicitSmallPhysical support perm left)
        (explicitSmallPhysical support perm right)

instance (support : Fin 11) (perm : Fin 120) :
    Decidable (ExplicitLargeCompatible support perm) := by
  unfold ExplicitLargeCompatible
  infer_instance

instance (support : Fin 60) (perm : Fin 24) :
    Decidable (ExplicitSmallCompatible support perm) := by
  unfold ExplicitSmallCompatible
  infer_instance

theorem largeCatalogue_compatible (index : Fin 110) :
    ExplicitLargeCompatible (largeCatalogueSupportIndex index)
      (largeCataloguePermIndex index) := by
  fin_cases index <;> decide

theorem smallCatalogue_compatible (index : Fin 120) :
    ExplicitSmallCompatible (smallCatalogueSupportIndex index)
      (smallCataloguePermIndex index) := by
  fin_cases index <;> decide

noncomputable def largeCatalogueChoice (index : Fin 110) :
    LargeFactorChoice where
  support := indexedLargeSupport (largeCatalogueSupportIndex index)
  perm := fivePermutationAt (largeCataloguePermIndex index)
  compatible := by
    intro left right hne
    rw [← explicitLargeLabelOrder_eq, ← explicitLargeLabelOrder_eq,
      ← explicitLargeSupportOrder_eq, ← explicitLargeSupportOrder_eq]
    exact largeCatalogue_compatible index left right hne

noncomputable def smallCatalogueChoice (index : Fin 120) :
    SmallFactorChoice where
  support := indexedSmallSupport (smallCatalogueSupportIndex index)
  perm := fourPermutationAt (smallCataloguePermIndex index)
  compatible := by
    intro left right hne
    rw [← explicitSmallLabelOrder_eq, ← explicitSmallLabelOrder_eq,
      ← explicitSmallSupportOrder_eq, ← explicitSmallSupportOrder_eq]
    exact smallCatalogue_compatible index left right hne

theorem largeCatalogueChoice_physical
    (index : Fin 110) (position : Fin 5) :
    (largeCatalogueChoice index).physical position =
      largeCataloguePhysical index position := by
  rw [LargeFactorChoice.physical, largeCatalogueChoice,
    largeCataloguePhysical, explicitLargePhysical,
    ← explicitLargeSupportOrder_eq]

theorem smallCatalogueChoice_physical
    (index : Fin 120) (position : Fin 4) :
    (smallCatalogueChoice index).physical position =
      smallCataloguePhysical index position := by
  rw [SmallFactorChoice.physical, smallCatalogueChoice,
    smallCataloguePhysical, explicitSmallPhysical,
    ← explicitSmallSupportOrder_eq]

/-! ## Completeness of the explicit labelled catalogues -/

theorem explicitLargeCompatible_covered :
    ∀ support : Fin 11, ∀ perm : Fin 120,
      ExplicitLargeCompatible support perm →
        ∃ index : Fin 110,
          largeCatalogueSupportIndex index = support ∧
          largeCataloguePermIndex index = perm := by
  decide

theorem explicitSmallCompatible_covered :
    ∀ support : Fin 60, ∀ perm : Fin 24,
      ExplicitSmallCompatible support perm →
        ∃ index : Fin 120,
          smallCatalogueSupportIndex index = support ∧
          smallCataloguePermIndex index = perm := by
  decide

theorem exists_largeCatalogueIndex (choice : LargeFactorChoice) :
    ∃ index : Fin 110,
      choice.support = (largeCatalogueChoice index).support ∧
      ∀ position : Fin 5,
        choice.physical position = largeCataloguePhysical index position := by
  obtain ⟨support, hsupport⟩ :=
    indexedLargeSupport_surjective choice.support
  let perm := fivePermutationIndex choice.perm
  have hperm : fivePermutationAt perm = choice.perm :=
    fivePermutationAt_index choice.perm
  have hphysical : ∀ position : Fin 5,
      choice.physical position =
        explicitLargePhysical support perm position := by
    intro position
    rw [LargeFactorChoice.physical, explicitLargePhysical,
      ← hsupport, ← hperm, ← explicitLargeSupportOrder_eq]
  have hcompatible : ExplicitLargeCompatible support perm := by
    intro left right hne
    have h := choice.compatible left right hne
    rw [← explicitLargeLabelOrder_eq, ← explicitLargeLabelOrder_eq] at h
    change k15Template true (explicitLargeLabelOrder left)
        (explicitLargeLabelOrder right) =
      twistedRoot4LargePhysicalColoring (choice.physical left)
        (choice.physical right) at h
    rw [hphysical left, hphysical right] at h
    exact h
  obtain ⟨index, hindexSupport, hindexPerm⟩ :=
    explicitLargeCompatible_covered support perm hcompatible
  refine ⟨index, ?_, ?_⟩
  · change choice.support =
      indexedLargeSupport (largeCatalogueSupportIndex index)
    rw [hindexSupport, hsupport]
  · intro position
    rw [hphysical, largeCataloguePhysical, explicitLargePhysical,
      hindexSupport, hindexPerm]
    rfl

theorem exists_smallCatalogueIndex (choice : SmallFactorChoice) :
    ∃ index : Fin 120,
      choice.support = (smallCatalogueChoice index).support ∧
      ∀ position : Fin 4,
        choice.physical position = smallCataloguePhysical index position := by
  obtain ⟨support, hsupport⟩ :=
    indexedSmallSupport_surjective choice.support
  let perm := fourPermutationIndex choice.perm
  have hperm : fourPermutationAt perm = choice.perm :=
    fourPermutationAt_index choice.perm
  have hphysical : ∀ position : Fin 4,
      choice.physical position =
        explicitSmallPhysical support perm position := by
    intro position
    rw [SmallFactorChoice.physical, explicitSmallPhysical,
      ← hsupport, ← hperm, ← explicitSmallSupportOrder_eq]
  have hcompatible : ExplicitSmallCompatible support perm := by
    intro left right hne
    have h := choice.compatible left right hne
    rw [← explicitSmallLabelOrder_eq, ← explicitSmallLabelOrder_eq] at h
    change k15Template true (explicitSmallLabelOrder left)
        (explicitSmallLabelOrder right) =
      twistedRoot4SmallPhysicalColoring (choice.physical left)
        (choice.physical right) at h
    rw [hphysical left, hphysical right] at h
    exact h
  obtain ⟨index, hindexSupport, hindexPerm⟩ :=
    explicitSmallCompatible_covered support perm hcompatible
  refine ⟨index, ?_, ?_⟩
  · change choice.support =
      indexedSmallSupport (smallCatalogueSupportIndex index)
    rw [hindexSupport, hsupport]
  · intro position
    rw [hphysical, smallCataloguePhysical, explicitSmallPhysical,
      hindexSupport, hindexPerm]
    rfl

/-! ## Independent physical orbit normalizers: `110 → 11`, `120 → 12` -/

def largeNormalizerWord : Fin 110 → Nat :=
  ![0, 88, 1, 2, 3, 4, 90, 89, 91, 92,
    5, 6, 7, 8, 60, 61, 63, 62, 9, 64,
    94, 93, 39, 38, 97, 42, 95, 96, 40, 41,
    85, 84, 86, 75, 72, 71, 73, 74, 83, 82,
    10, 87, 32, 54, 76, 21, 98, 109, 65, 43,
    79, 78, 46, 45, 80, 81, 48, 47, 44, 77,
    15, 14, 11, 99, 103, 102, 12, 13, 100, 101,
    66, 55, 70, 69, 59, 58, 68, 67, 57, 56,
    53, 20, 17, 16, 52, 51, 18, 19, 49, 50,
    25, 26, 23, 24, 22, 33, 34, 35, 36, 37,
    104, 105, 29, 30, 27, 28, 107, 106, 108, 31]

def smallNormalizerWord : Fin 120 → Nat :=
  ![0, 1, 2, 3, 4, 64, 5, 6, 96, 97, 7, 8,
    9, 69, 98, 99, 66, 65, 102, 101, 42, 41, 100, 40,
    105, 45, 104, 103, 79, 80, 89, 90, 92, 91, 10, 106,
    76, 88, 67, 68, 11, 107, 35, 47, 95, 59, 94, 58,
    84, 85, 48, 49, 23, 119, 87, 86, 77, 78, 15, 14,
    110, 111, 13, 12, 21, 57, 22, 118, 74, 75, 62, 63,
    73, 72, 81, 93, 61, 60, 20, 19, 54, 53, 117, 33,
    17, 18, 25, 24, 27, 26, 56, 55, 34, 46, 38, 39,
    82, 70, 112, 28, 30, 29, 16, 52, 115, 116, 114, 113,
    109, 108, 31, 32, 36, 37, 83, 71, 51, 50, 44, 43]

def largeNormalizerRepresentative (source : Fin 110) : Fin 11 :=
  Fin.ofNat 11 (largeNormalizerWord source % 11)

def largeNormalizerAction (source : Fin 110) : Fin 10 :=
  Fin.ofNat 10 (largeNormalizerWord source / 11)

def smallNormalizerRepresentative (source : Fin 120) : Fin 12 :=
  Fin.ofNat 12 (smallNormalizerWord source % 12)

def smallNormalizerAction (source : Fin 120) : Fin 10 :=
  Fin.ofNat 10 (smallNormalizerWord source / 12)

def largeRepresentativeRawIndex : Fin 11 → Fin 110 :=
  ![0, 2, 3, 4, 5, 10, 11, 12, 13, 18, 40]

def smallRepresentativeRawIndex : Fin 12 → Fin 120 :=
  ![0, 1, 2, 3, 4, 6, 7, 10, 11, 12, 34, 40]

noncomputable def largePhysicalRepresentative (index : Fin 11) :
    LargeFactorChoice :=
  largeCatalogueChoice (largeRepresentativeRawIndex index)

noncomputable def smallPhysicalRepresentative (index : Fin 12) :
    SmallFactorChoice :=
  smallCatalogueChoice (smallRepresentativeRawIndex index)

theorem largeNormalizerEquationExplicit :
    ∀ source : Fin 110, ∀ position : Fin 5,
      largeCataloguePhysical
          (largeRepresentativeRawIndex
            (largeNormalizerRepresentative source)) position =
        physicalK15Map (largeNormalizerAction source)
          (largeCataloguePhysical source position) := by
  decide

theorem smallNormalizerEquationExplicit :
    ∀ source : Fin 120, ∀ position : Fin 4,
      smallCataloguePhysical
          (smallRepresentativeRawIndex
            (smallNormalizerRepresentative source)) position =
        physicalK15Map (smallNormalizerAction source)
          (smallCataloguePhysical source position) := by
  decide

theorem largeNormalizerEquation
    (source : Fin 110) (position : Fin 5) :
    (largePhysicalRepresentative
        (largeNormalizerRepresentative source)).physical position =
      physicalK15Equiv (largeNormalizerAction source)
        (largeCataloguePhysical source position) := by
  rw [largePhysicalRepresentative, largeCatalogueChoice_physical]
  exact largeNormalizerEquationExplicit source position

theorem smallNormalizerEquation
    (source : Fin 120) (position : Fin 4) :
    (smallPhysicalRepresentative
        (smallNormalizerRepresentative source)).physical position =
      physicalK15Equiv (smallNormalizerAction source)
        (smallCataloguePhysical source position) := by
  rw [smallPhysicalRepresentative, smallCatalogueChoice_physical]
  exact smallNormalizerEquationExplicit source position

/-- The identity free permutation is not compatible with the twisted
root-4 template; the swap of positions `1` and `2` is the first compatible
free permutation in the Lean enumeration order. -/
theorem freeRepresentative_compatible :
    FreePermutationCompatible (Equiv.swap (1 : FiveVertex) 2) := by
  intro left right hne
  rw [← explicitFreeLabelOrder_eq, ← explicitFreeLabelOrder_eq]
  fin_cases left <;> fin_cases right <;> simp_all <;> decide

def freePhysicalRepresentative : FreeFactorChoice :=
  ⟨Equiv.swap (1 : FiveVertex) 2, freeRepresentative_compatible⟩

theorem exists_independentPhysicalNormalization
    (sourceLarge : LargeFactorChoice)
    (sourceSmall : SmallFactorChoice) :
    ∃ largeIndex : Fin 11, ∃ smallIndex : Fin 12,
      Nonempty (PhysicalNormalizationWitness sourceLarge
        (largePhysicalRepresentative largeIndex) sourceSmall
        (smallPhysicalRepresentative smallIndex)) := by
  obtain ⟨largeSource, _hlargeSupport, hlargePhysical⟩ :=
    exists_largeCatalogueIndex sourceLarge
  obtain ⟨smallSource, _hsmallSupport, hsmallPhysical⟩ :=
    exists_smallCatalogueIndex sourceSmall
  let largeIndex := largeNormalizerRepresentative largeSource
  let smallIndex := smallNormalizerRepresentative smallSource
  let largeAction := largeNormalizerAction largeSource
  let smallAction := smallNormalizerAction smallSource
  have hlarge : ∀ position : Fin 5,
      (largePhysicalRepresentative largeIndex).physical position =
        physicalK15Equiv largeAction (sourceLarge.physical position) := by
    intro position
    calc
      _ = physicalK15Equiv largeAction
          (largeCataloguePhysical largeSource position) :=
        largeNormalizerEquation largeSource position
      _ = _ := congrArg (physicalK15Equiv largeAction)
        (hlargePhysical position).symm
  have hsmall : ∀ position : Fin 4,
      (smallPhysicalRepresentative smallIndex).physical position =
        physicalK15Equiv smallAction (sourceSmall.physical position) := by
    intro position
    calc
      _ = physicalK15Equiv smallAction
          (smallCataloguePhysical smallSource position) :=
        smallNormalizerEquation smallSource position
      _ = _ := congrArg (physicalK15Equiv smallAction)
        (hsmallPhysical position).symm
  exact ⟨largeIndex, smallIndex, ⟨
    PhysicalNormalizationWitness.ofPhysicalEquations
      sourceLarge (largePhysicalRepresentative largeIndex)
      sourceSmall (smallPhysicalRepresentative smallIndex)
      largeAction smallAction hlarge hsmall⟩⟩

/-! ## The exact 132 representative pairs and coverage

The root-4 normal-template stabilizer is trivial (no rooted involution), so
the diagonal quotient is the full `11 × 12` product: all `132` pairs are
representatives and coverage is the direct enumeration. -/

def quotientRepresentativePair : Fin 132 → Fin 11 × Fin 12 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5),
    (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11),
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5),
    (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11),
    (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5),
    (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11),
    (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5),
    (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11),
    (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5),
    (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11),
    (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5),
    (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11),
    (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5),
    (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11),
    (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5),
    (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11),
    (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5),
    (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11)]

theorem quotientRepresentativePair_coverage :
    ∀ largeIndex : Fin 11, ∀ smallIndex : Fin 12,
      ∃ representative : Fin 132,
        largeIndex = (quotientRepresentativePair representative).1 ∧
        smallIndex = (quotientRepresentativePair representative).2 := by
  decide

theorem factorAssignmentRealization_reduces_to_132
    {branch : CanonicalBranch .uut 2 (Fin.last 15)}
    {sourceFree : FreeFactorChoice}
    {sourceLarge : LargeFactorChoice}
    {sourceSmall : SmallFactorChoice}
    (realization : FactorAssignmentRealization branch
      sourceFree sourceLarge sourceSmall) :
    ∃ representative : Fin 132,
      ∃ normalized : CanonicalBranch .uut 2 (Fin.last 15),
        FactorAssignmentRealization normalized freePhysicalRepresentative
          (largePhysicalRepresentative
            (quotientRepresentativePair representative).1)
          (smallPhysicalRepresentative
            (quotientRepresentativePair representative).2) := by
  obtain ⟨largeIndex, smallIndex, ⟨physicalWitness⟩⟩ :=
    exists_independentPhysicalNormalization sourceLarge sourceSmall
  let firstBranch := normalizedBranch branch sourceFree
    freePhysicalRepresentative physicalWitness
  have firstRealization : FactorAssignmentRealization firstBranch
      freePhysicalRepresentative (largePhysicalRepresentative largeIndex)
      (smallPhysicalRepresentative smallIndex) :=
    realization.normalize physicalWitness
  obtain ⟨representative, hlarge, hsmall⟩ :=
    quotientRepresentativePair_coverage largeIndex smallIndex
  subst hlarge
  subst hsmall
  exact ⟨representative, firstBranch, firstRealization⟩

theorem twistedRoot4Realization_reduces_to_132
    (realization : TwistedRoot4Realization) :
    ∃ representative : Fin 132,
      ∃ normalized : CanonicalBranch .uut 2 (Fin.last 15),
        FactorAssignmentRealization normalized freePhysicalRepresentative
          (largePhysicalRepresentative
            (quotientRepresentativePair representative).1)
          (smallPhysicalRepresentative
            (quotientRepresentativePair representative).2) := by
  obtain ⟨data⟩ := exists_canonicalStrongData realization
  exact factorAssignmentRealization_reduces_to_132
    (semantic_factorAssignmentRealization realization data)

#print axioms explicitFreeLabelOrder_eq
#print axioms explicitLargeLabelOrder_eq
#print axioms explicitSmallLabelOrder_eq
#print axioms largeCatalogue_compatible
#print axioms smallCatalogue_compatible
#print axioms largeCatalogueChoice_physical
#print axioms smallCatalogueChoice_physical
#print axioms explicitLargeCompatible_covered
#print axioms explicitSmallCompatible_covered
#print axioms exists_largeCatalogueIndex
#print axioms exists_smallCatalogueIndex
#print axioms largeNormalizerEquationExplicit
#print axioms smallNormalizerEquationExplicit
#print axioms largeNormalizerEquation
#print axioms smallNormalizerEquation
#print axioms freeRepresentative_compatible
#print axioms exists_independentPhysicalNormalization
#print axioms quotientRepresentativePair_coverage
#print axioms factorAssignmentRealization_reduces_to_132
#print axioms twistedRoot4Realization_reduces_to_132

end UUTD9Root4Orbit
end R4333
