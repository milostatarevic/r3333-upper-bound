import PricingG.UUTD9Root12Factor

/-! Continuation-authored (locks/duuu), 2026-08-05. Twisted root-12 root
stabilizer, role-aware clone (all template sites label-side -> true; the
stabilizer involution, label sets, and induced index actions replaced with
the verified twisted-root-12 data). -/

/-!
# Rooted normal-template stabilizer in the twisted root-12 degree-nine case

The twisted critical `K15` has one nonidentity colour-preserving
automorphism fixing the normalized root label `12`.  This file packages that
map and its induced action on the three factor catalogues.  All tables and
all preservation facts are checked by kernel reduction.
-/

namespace R4333
namespace UUTD9Root12Stabilizer

open UUTD9Root12Case
open UUTD9Root12CNF
open UUTD9Root12Factor

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rootFlipMap : Fin 15 → Fin 15 :=
  ![3, 11, 8, 0, 13, 5, 6, 14, 2, 10, 9, 1, 12, 4, 7]

theorem rootFlipMap_bijective : Function.Bijective rootFlipMap := by
  decide

theorem rootFlipMap_involutive (position : Fin 15) :
    rootFlipMap (rootFlipMap position) = position := by
  fin_cases position <;> decide

theorem rootFlipMap_preserves (left right : Fin 15) (hne : left ≠ right) :
    k15Template true (rootFlipMap left) (rootFlipMap right) =
      k15Template true left right := by
  fin_cases left <;> fin_cases right <;> simp_all <;> decide

theorem rootFlipMap_root : rootFlipMap 12 = 12 := by decide

noncomputable def rootFlipEquiv : Equiv.Perm (Fin 15) :=
  Equiv.ofBijective rootFlipMap rootFlipMap_bijective

def rootFreeAction : Fin 5 → Fin 5 := ![1, 0, 4, 3, 2]
def rootLargeAction : Fin 5 → Fin 5 := ![4, 1, 3, 2, 0]
def rootSmallAction : Fin 4 → Fin 4 := ![2, 3, 0, 1]

theorem rootFreeAction_bijective : Function.Bijective rootFreeAction := by
  decide

theorem rootLargeAction_bijective : Function.Bijective rootLargeAction := by
  decide

theorem rootSmallAction_bijective : Function.Bijective rootSmallAction := by
  decide

theorem rootFreeAction_involutive (position : Fin 5) :
    rootFreeAction (rootFreeAction position) = position := by
  fin_cases position <;> decide

theorem rootLargeAction_involutive (position : Fin 5) :
    rootLargeAction (rootLargeAction position) = position := by
  fin_cases position <;> decide

theorem rootSmallAction_involutive (position : Fin 4) :
    rootSmallAction (rootSmallAction position) = position := by
  fin_cases position <;> decide

noncomputable def rootFreeEquiv : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective rootFreeAction rootFreeAction_bijective

noncomputable def rootLargeEquiv : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective rootLargeAction rootLargeAction_bijective

noncomputable def rootSmallEquiv : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective rootSmallAction rootSmallAction_bijective

def explicitFreeLabelOrder : Fin 5 → Fin 15 := ![0, 3, 4, 6, 13]
def explicitLargeLabelOrder : Fin 5 → Fin 15 := ![1, 5, 9, 10, 11]
def explicitSmallLabelOrder : Fin 4 → Fin 15 := ![2, 7, 8, 14]

private theorem explicitFreeLabelOrder_mem (position : Fin 5) :
    explicitFreeLabelOrder position ∈ twistedRoot12FreeLabelSet := by
  fin_cases position <;> decide

private theorem explicitLargeLabelOrder_mem (position : Fin 5) :
    explicitLargeLabelOrder position ∈ twistedRoot12LargeLabelSet := by
  fin_cases position <;> decide

private theorem explicitSmallLabelOrder_mem (position : Fin 4) :
    explicitSmallLabelOrder position ∈ twistedRoot12SmallLabelSet := by
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
      twistedRoot12FreeLabelSet.orderEmbOfFin twistedRoot12FreeLabelSet_card :=
    Finset.orderEmbOfFin_unique twistedRoot12FreeLabelSet_card
      explicitFreeLabelOrder_mem explicitFreeLabelOrder_strictMono
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

theorem explicitLargeLabelOrder_eq (position : Fin 5) :
    explicitLargeLabelOrder position = (largeLabelOrder position).1 := by
  have hfun : explicitLargeLabelOrder =
      twistedRoot12LargeLabelSet.orderEmbOfFin twistedRoot12LargeLabelSet_card :=
    Finset.orderEmbOfFin_unique twistedRoot12LargeLabelSet_card
      explicitLargeLabelOrder_mem explicitLargeLabelOrder_strictMono
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

theorem explicitSmallLabelOrder_eq (position : Fin 4) :
    explicitSmallLabelOrder position = (smallLabelOrder position).1 := by
  have hfun : explicitSmallLabelOrder =
      twistedRoot12SmallLabelSet.orderEmbOfFin twistedRoot12SmallLabelSet_card :=
    Finset.orderEmbOfFin_unique twistedRoot12SmallLabelSet_card
      explicitSmallLabelOrder_mem explicitSmallLabelOrder_strictMono
  have h := congrFun hfun position
  rw [← Finset.coe_orderIsoOfFin_apply] at h
  exact h

theorem rootFlip_freeLabelOrder (position : Fin 5) :
    rootFlipMap (freeLabelOrder position).1 =
      (freeLabelOrder (rootFreeAction position)).1 := by
  rw [← explicitFreeLabelOrder_eq, ← explicitFreeLabelOrder_eq]
  fin_cases position <;> decide

theorem rootFlip_largeLabelOrder (position : Fin 5) :
    rootFlipMap (largeLabelOrder position).1 =
      (largeLabelOrder (rootLargeAction position)).1 := by
  rw [← explicitLargeLabelOrder_eq, ← explicitLargeLabelOrder_eq]
  fin_cases position <;> decide

theorem rootFlip_smallLabelOrder (position : Fin 4) :
    rootFlipMap (smallLabelOrder position).1 =
      (smallLabelOrder (rootSmallAction position)).1 := by
  rw [← explicitSmallLabelOrder_eq, ← explicitSmallLabelOrder_eq]
  fin_cases position <;> decide

theorem rootFlip_largeLabelOrder_inverse (position : Fin 5) :
    (largeLabelOrder position).1 =
      rootFlipMap (largeLabelOrder (rootLargeAction position)).1 := by
  rw [rootFlip_largeLabelOrder, rootLargeAction_involutive]

theorem rootFlip_smallLabelOrder_inverse (position : Fin 4) :
    (smallLabelOrder position).1 =
      rootFlipMap (smallLabelOrder (rootSmallAction position)).1 := by
  rw [rootFlip_smallLabelOrder, rootSmallAction_involutive]

noncomputable def rootFlipFreeChoice
    (choice : FreeFactorChoice) : FreeFactorChoice :=
  ⟨choice.1.trans rootFreeEquiv, by
    intro left right hne
    change k15Template true
        (freeLabelOrder (rootFreeAction (choice.1 left))).1
        (freeLabelOrder (rootFreeAction (choice.1 right))).1 = _
    rw [← rootFlip_freeLabelOrder, ← rootFlip_freeLabelOrder,
      rootFlipMap_preserves]
    · exact choice.2 left right hne
    · intro hlabels
      apply hne
      apply choice.1.injective
      apply freeLabelOrder.injective
      exact Subtype.ext hlabels⟩

noncomputable def rootFlipLargeChoice
    (choice : LargeFactorChoice) : LargeFactorChoice where
  support := choice.support
  perm := rootLargeEquiv.trans choice.perm
  compatible := by
    intro left right hne
    have haction : rootLargeAction left ≠ rootLargeAction right :=
      rootLargeAction_bijective.1.ne hne
    have hold := choice.compatible
      (rootLargeAction left) (rootLargeAction right) haction
    change k15Template true (largeLabelOrder left).1
        (largeLabelOrder right).1 =
      twistedRoot12LargePhysicalColoring
        (largeFactorOrder choice.support
          (choice.perm (rootLargeAction left))).1
        (largeFactorOrder choice.support
          (choice.perm (rootLargeAction right))).1
    calc
      k15Template true (largeLabelOrder left).1
          (largeLabelOrder right).1 =
          k15Template true
            (rootFlipMap
              (largeLabelOrder (rootLargeAction left)).1)
            (rootFlipMap
              (largeLabelOrder (rootLargeAction right)).1) := by
        rw [rootFlip_largeLabelOrder, rootFlip_largeLabelOrder,
          rootLargeAction_involutive, rootLargeAction_involutive]
      _ = k15Template true
            (largeLabelOrder (rootLargeAction left)).1
            (largeLabelOrder (rootLargeAction right)).1 := by
        apply rootFlipMap_preserves
        intro hlabels
        apply haction
        apply largeLabelOrder.injective
        exact Subtype.ext hlabels
      _ = _ := hold

noncomputable def rootFlipSmallChoice
    (choice : SmallFactorChoice) : SmallFactorChoice where
  support := choice.support
  perm := rootSmallEquiv.trans choice.perm
  compatible := by
    intro left right hne
    have haction : rootSmallAction left ≠ rootSmallAction right :=
      rootSmallAction_bijective.1.ne hne
    have hold := choice.compatible
      (rootSmallAction left) (rootSmallAction right) haction
    change k15Template true (smallLabelOrder left).1
        (smallLabelOrder right).1 =
      twistedRoot12SmallPhysicalColoring
        (smallFactorOrder choice.support
          (choice.perm (rootSmallAction left))).1
        (smallFactorOrder choice.support
          (choice.perm (rootSmallAction right))).1
    calc
      k15Template true (smallLabelOrder left).1
          (smallLabelOrder right).1 =
          k15Template true
            (rootFlipMap
              (smallLabelOrder (rootSmallAction left)).1)
            (rootFlipMap
              (smallLabelOrder (rootSmallAction right)).1) := by
        rw [rootFlip_smallLabelOrder, rootFlip_smallLabelOrder,
          rootSmallAction_involutive, rootSmallAction_involutive]
      _ = k15Template true
            (smallLabelOrder (rootSmallAction left)).1
            (smallLabelOrder (rootSmallAction right)).1 := by
        apply rootFlipMap_preserves
        intro hlabels
        apply haction
        apply smallLabelOrder.injective
        exact Subtype.ext hlabels
      _ = _ := hold

theorem rootFlipFreeChoice_label
    (choice : FreeFactorChoice) (position : Fin 5) :
    (rootFlipFreeChoice choice).label position =
      rootFlipMap (choice.label position) := by
  rw [FreeFactorChoice.label, FreeFactorChoice.label]
  exact (rootFlip_freeLabelOrder (choice.1 position)).symm

theorem rootFlipLargeChoice_physical
    (choice : LargeFactorChoice) (position : Fin 5) :
    (rootFlipLargeChoice choice).physical position =
      choice.physical (rootLargeAction position) := by
  rfl

theorem rootFlipSmallChoice_physical
    (choice : SmallFactorChoice) (position : Fin 4) :
    (rootFlipSmallChoice choice).physical position =
      choice.physical (rootSmallAction position) := by
  rfl

private theorem freeLabelOrder_ne_largeLabelOrder
    (freeIndex largeIndex : Fin 5) :
    (freeLabelOrder freeIndex).1 ≠ (largeLabelOrder largeIndex).1 := by
  rw [← explicitFreeLabelOrder_eq, ← explicitLargeLabelOrder_eq]
  fin_cases freeIndex <;> fin_cases largeIndex <;> decide

private theorem freeLabelOrder_ne_smallLabelOrder
    (freeIndex : Fin 5) (smallIndex : Fin 4) :
    (freeLabelOrder freeIndex).1 ≠ (smallLabelOrder smallIndex).1 := by
  rw [← explicitFreeLabelOrder_eq, ← explicitSmallLabelOrder_eq]
  fin_cases freeIndex <;> fin_cases smallIndex <;> decide

private theorem largeLabelOrder_ne_smallLabelOrder
    (largeIndex : Fin 5) (smallIndex : Fin 4) :
    (largeLabelOrder largeIndex).1 ≠ (smallLabelOrder smallIndex).1 := by
  rw [← explicitLargeLabelOrder_eq, ← explicitSmallLabelOrder_eq]
  fin_cases largeIndex <;> fin_cases smallIndex <;> decide

theorem rootFlip_freeLarge_color
    (free : FreeFactorChoice) (large : LargeFactorChoice)
    (freeIndex : Fin 5) (largeIndex : Fin 5) :
    k15Template true
        ((rootFlipFreeChoice free).label freeIndex)
        ((rootFlipLargeChoice large).label largeIndex) =
      k15Template true
        (free.label freeIndex)
        (large.label (rootLargeAction largeIndex)) := by
  rw [rootFlipFreeChoice_label]
  change k15Template true (rootFlipMap (free.label freeIndex))
      (largeLabelOrder largeIndex).1 =
    k15Template true (free.label freeIndex)
      (largeLabelOrder (rootLargeAction largeIndex)).1
  calc
    _ = k15Template true (rootFlipMap (free.label freeIndex))
          (rootFlipMap
            (largeLabelOrder (rootLargeAction largeIndex)).1) := by
      rw [rootFlip_largeLabelOrder_inverse]
    _ = _ := by
      apply rootFlipMap_preserves
      exact freeLabelOrder_ne_largeLabelOrder
        (free.1 freeIndex) (rootLargeAction largeIndex)

theorem rootFlip_freeSmall_color
    (free : FreeFactorChoice) (small : SmallFactorChoice)
    (freeIndex : Fin 5) (smallIndex : Fin 4) :
    k15Template true
        ((rootFlipFreeChoice free).label freeIndex)
        ((rootFlipSmallChoice small).label smallIndex) =
      k15Template true
        (free.label freeIndex)
        (small.label (rootSmallAction smallIndex)) := by
  rw [rootFlipFreeChoice_label]
  change k15Template true (rootFlipMap (free.label freeIndex))
      (smallLabelOrder smallIndex).1 =
    k15Template true (free.label freeIndex)
      (smallLabelOrder (rootSmallAction smallIndex)).1
  calc
    _ = k15Template true (rootFlipMap (free.label freeIndex))
          (rootFlipMap
            (smallLabelOrder (rootSmallAction smallIndex)).1) := by
      rw [rootFlip_smallLabelOrder_inverse]
    _ = _ := by
      apply rootFlipMap_preserves
      exact freeLabelOrder_ne_smallLabelOrder
        (free.1 freeIndex) (rootSmallAction smallIndex)

theorem rootFlip_largeSmall_color
    (large : LargeFactorChoice) (small : SmallFactorChoice)
    (largeIndex : Fin 5) (smallIndex : Fin 4) :
    k15Template true
        ((rootFlipLargeChoice large).label largeIndex)
        ((rootFlipSmallChoice small).label smallIndex) =
      k15Template true
        (large.label (rootLargeAction largeIndex))
        (small.label (rootSmallAction smallIndex)) := by
  change k15Template true (largeLabelOrder largeIndex).1
      (smallLabelOrder smallIndex).1 =
    k15Template true
      (largeLabelOrder (rootLargeAction largeIndex)).1
      (smallLabelOrder (rootSmallAction smallIndex)).1
  calc
    _ = k15Template true
          (rootFlipMap
            (largeLabelOrder (rootLargeAction largeIndex)).1)
          (rootFlipMap
            (smallLabelOrder (rootSmallAction smallIndex)).1) := by
      rw [rootFlip_largeLabelOrder_inverse, rootFlip_smallLabelOrder_inverse]
    _ = _ := by
      apply rootFlipMap_preserves
      exact largeLabelOrder_ne_smallLabelOrder
        (rootLargeAction largeIndex) (rootSmallAction smallIndex)

#print axioms rootFlipMap_preserves
#print axioms rootFlipFreeChoice
#print axioms rootFlipLargeChoice
#print axioms rootFlipSmallChoice
#print axioms rootFlip_freeLarge_color
#print axioms rootFlip_freeSmall_color
#print axioms rootFlip_largeSmall_color

end UUTD9Root12Stabilizer
end R4333
