import R4333Lean.ProfileDRowSupportBounds61

/-!
# Strategic four-row restrictions in profile D

The original four-row boundary retains the first four labels of the free
`K14`.  For incidence arguments it is useful to retain a prescribed free
vertex and three arbitrary companions instead.  This file provides that
semantic transport, including all native order-61 support floors.

No obstruction or finite-search conclusion is asserted.
-/

namespace R4333
namespace ProfileDFourRowStrategicRestriction

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDRowSupportBounds61

set_option maxRecDepth 1000000

/-- Restrict a full fourteen-row object along any injection of four labels. -/
def restrictFourWith {kind : Kind} (ext : Extension kind)
    (embedding : FourVertex ↪ FreeVertex) : FourExtension kind where
  tail := ext.tail
  inside := pullbackColoring ext.inside embedding
  rows := fun a ↦ ext.rows (embedding a)
  insideNoMono :=
    noMono_pullback ext.inside embedding embedding.injective ext.insideNoMono
  insideRootForbidden := by
    intro a b hab
    exact ext.insideRootForbidden (embedding a) (embedding b)
      (embedding.injective.ne hab)
  rowsAdmissible := fun a ↦ ext.rowsAdmissible (embedding a)
  rowsPairCompatible := by
    intro a b hab x hbad
    exact ext.rowsPairCompatible (embedding a) (embedding b)
      (embedding.injective.ne hab) x hbad

/-- The degree-floored version of an arbitrary injected restriction. -/
def restrictDegreeFlooredFourWith {kind : Kind} (ext : Extension kind)
    (embedding : FourVertex ↪ FreeVertex) :
    DegreeFlooredFourExtension kind where
  toFourExtension := restrictFourWith ext embedding
  zeroSupportLower := fun a ↦ row_zero_support_ge_eleven ext (embedding a)
  zeroSupportUpper := fun a ↦ row_zero_support_le_fifteen ext (embedding a)
  nonzeroSupportLower := fun a q hq ↦
    row_nonzero_support_ge_seven ext (embedding a) q hq
  nonzeroSupportUpper := fun a q hq ↦
    row_nonzero_support_le_thirteen ext (embedding a) q hq

/-- Put a prescribed free vertex in row zero, using a transposition of the
ordinary first-four embedding to obtain three distinct companions. -/
def fourEmbeddingAt (selected : FreeVertex) : FourVertex ↪ FreeVertex where
  toFun a := Equiv.swap selected 0 (fourEmbedding a)
  inj' := (Equiv.swap selected 0).injective.comp fourEmbedding_injective

@[simp] theorem fourEmbeddingAt_zero (selected : FreeVertex) :
    fourEmbeddingAt selected 0 = selected := by
  simp [fourEmbeddingAt, fourEmbedding]

def restrictFourAt {kind : Kind} (ext : Extension kind)
    (selected : FreeVertex) : FourExtension kind :=
  restrictFourWith ext (fourEmbeddingAt selected)

def restrictDegreeFlooredFourAt {kind : Kind} (ext : Extension kind)
    (selected : FreeVertex) : DegreeFlooredFourExtension kind :=
  restrictDegreeFlooredFourWith ext (fourEmbeddingAt selected)

@[simp] theorem restrictFourAt_row_zero {kind : Kind}
    (ext : Extension kind) (selected : FreeVertex) :
    (restrictFourAt ext selected).rows 0 = ext.rows selected := by
  simp [restrictFourAt, restrictFourWith]

@[simp] theorem restrictDegreeFlooredFourAt_row_zero {kind : Kind}
    (ext : Extension kind) (selected : FreeVertex) :
    (restrictDegreeFlooredFourAt ext selected).toFourExtension.rows 0 =
      ext.rows selected := by
  simp [restrictDegreeFlooredFourAt, restrictDegreeFlooredFourWith,
    restrictFourWith]

#print axioms R4333.ProfileDFourRowStrategicRestriction.restrictFourWith
#print axioms R4333.ProfileDFourRowStrategicRestriction.restrictDegreeFlooredFourWith
#print axioms R4333.ProfileDFourRowStrategicRestriction.fourEmbeddingAt
#print axioms R4333.ProfileDFourRowStrategicRestriction.restrictDegreeFlooredFourAt

end ProfileDFourRowStrategicRestriction
end R4333
