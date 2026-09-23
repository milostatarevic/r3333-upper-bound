import R4333Lean.ProfileDHighOwnFiveRowSplit61

/-!
# Exact inside structure of the profile-D four-support branch

In a four-support five-row object, the first four retained rows meet the
selected tail endpoint in its own root colour.  Their mutual edges therefore
avoid both that own colour and the distinguished root colour zero.  Hence the
inside K4 is an honest triangle-free two-colouring in the two remaining
colours.  This is the semantic entrance used by the restored-K15 quotient.
-/

namespace R4333
namespace ProfileDFourSupportInside61

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FourSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension

/-- The first four retained rows, forgetting the fifth row outside the
selected own-colour support. -/
def firstFourInsideColoring {kind : Kind}
    (ext : FourSupportExtension kind) : EdgeColoring (Fin 4) (Fin 4) :=
  pullbackColoring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
    Fin.castSuccEmb

theorem firstFourInsideColoring_noMono {kind : Kind}
    (ext : FourSupportExtension kind) :
    NoMonochromaticTriangle (firstFourInsideColoring ext) := by
  exact noMono_pullback
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
    Fin.castSuccEmb Fin.castSuccEmb.injective
    ext.toDegreeFlooredFiveExtension.toFiveExtension.insideNoMono

theorem firstFourInsideColoring_ne_zero {kind : Kind}
    (ext : FourSupportExtension kind) (a b : Fin 4) (hab : a ≠ b) :
    firstFourInsideColoring ext a b ≠ 0 := by
  apply ext.toDegreeFlooredFiveExtension.toFiveExtension.insideRootForbidden
  exact Fin.castSuccEmb.injective.ne hab

/-- Two support rows share the selected endpoint in its own colour, so their
mutual edge cannot use that colour. -/
theorem firstFourInsideColoring_ne_own {kind : Kind}
    (ext : FourSupportExtension kind) (a b : Fin 4) (hab : a ≠ b) :
    firstFourInsideColoring ext a b ≠ blockRootColor ext.block := by
  intro hedge
  apply ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsPairCompatible
    a.castSucc b.castSucc (Fin.castSuccEmb.injective.ne hab)
    (blockVertex ext.block ext.position.val)
  exact ⟨hedge.trans (ext.firstFourOwn a).symm,
    (ext.firstFourOwn a).trans (ext.firstFourOwn b).symm⟩

/-- Every off-diagonal first-four edge uses one of the two colours
complementary to zero and the selected block's root colour. -/
theorem firstFourInsideColoring_is_remaining {kind : Kind}
    (ext : FourSupportExtension kind) (a b : Fin 4) (hab : a ≠ b) :
    firstFourInsideColoring ext a b = firstRemainingColor ext.block ∨
      firstFourInsideColoring ext a b = secondRemainingColor ext.block := by
  apply remainingColor_cases ext.block
  · exact firstFourInsideColoring_ne_zero ext a b hab
  · exact firstFourInsideColoring_ne_own ext a b hab

/-- Boolean encoding of the exact two-colour inside K4. -/
def firstFourInsideBoolColoring {kind : Kind}
    (ext : FourSupportExtension kind) : EdgeColoring (Fin 4) Bool where
  color a b := encodeRemainingColor ext.block
    (firstFourInsideColoring ext a b)
  color_symm := by
    intro a b
    exact congrArg (encodeRemainingColor ext.block)
      ((firstFourInsideColoring ext).color_symm a b)

theorem firstFourInsideBoolColoring_noMono {kind : Kind}
    (ext : FourSupportExtension kind) :
    NoMonochromaticTriangle (firstFourInsideBoolColoring ext) := by
  intro a b c habc hmono
  apply firstFourInsideColoring_noMono ext a b c habc
  refine ⟨?_, ?_⟩
  · apply encodeRemainingColor_injective_on_remaining ext.block _ _
      (firstFourInsideColoring_is_remaining ext a b habc.1)
      (firstFourInsideColoring_is_remaining ext a c habc.2.1)
    simpa [firstFourInsideBoolColoring] using hmono.1
  · apply encodeRemainingColor_injective_on_remaining ext.block _ _
      (firstFourInsideColoring_is_remaining ext a c habc.2.1)
      (firstFourInsideColoring_is_remaining ext b c habc.2.2)
    simpa [firstFourInsideBoolColoring] using hmono.2

#print axioms firstFourInsideColoring_ne_own
#print axioms firstFourInsideColoring_is_remaining
#print axioms firstFourInsideBoolColoring_noMono

end ProfileDFourSupportInside61
end R4333
