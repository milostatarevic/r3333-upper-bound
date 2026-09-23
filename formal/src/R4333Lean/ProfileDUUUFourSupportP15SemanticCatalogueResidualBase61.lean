import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueFinite61

/-!
# Residual-coordinate interface for the factorized P15 catalogue

This light module packages the generated local action which sends a reduced
rooted labeling to its stored ordered-leaf coordinate order.  The nine heavy
finite checks live in separate, cacheable support-pair modules.
-/

namespace R4333
namespace ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61

open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUFourSupportP0OrbitData61
open ProfileDUUUFourSupportP15SemanticCatalogueData61
open ProfileDUUUFourSupportP15SemanticCatalogueFinite61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev RootCase :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.RootCase

abbrev ReducedLabel :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.ReducedLabel

def residualCoordinate (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) : Fin 14 → Fin 14 :=
  localCoordinateAction (pairFirst pair) (pairSecond pair)
    (residualFreeAction pair root first second)
    (residualFirstAction pair root first second)
    (residualSecondAction pair root first second)

noncomputable def residualCoordinateEquiv (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) : Equiv.Perm (Fin 14) :=
  localCoordinateEquiv (pairFirst pair) (pairSecond pair)
    (residualFreeAction pair root first second)
    (residualFirstAction pair root first second)
    (residualSecondAction pair root first second)

@[simp] theorem residualCoordinateEquiv_apply (pair : Fin 9)
    (root : RootCase) (first second : ReducedLabel) (p : Fin 14) :
    residualCoordinateEquiv pair root first second p =
      residualCoordinate pair root first second p := by
  exact localCoordinateEquiv_apply _ _ _ _ _ _

def ResidualExactAt (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) : Prop :=
  ∀ left right : Fin 14, left ≠ right →
    reducedCandidateColor pair root first second
        (residualCoordinate pair root first second left)
        (residualCoordinate pair root first second right) =
      orderedMatrixColor (reducedLeaf pair root first second) left right

def ResidualUpperExactAt (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) : Prop :=
  ∀ left right : Fin 14, left.val < right.val →
    reducedCandidateColor pair root first second
        (residualCoordinate pair root first second left)
        (residualCoordinate pair root first second right) =
      orderedMatrixColor (reducedLeaf pair root first second) left right

instance (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) :
    Decidable (ResidualUpperExactAt pair root first second) := by
  unfold ResidualUpperExactAt
  infer_instance

theorem reducedCandidateColor_symm (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) (left right : Fin 14) :
    reducedCandidateColor pair root first second left right =
      reducedCandidateColor pair root first second right left := by
  unfold reducedCandidateColor
  exact congrArg (SingleRootStarCNF.canonicalPalette 3)
    ((k15Template (rootTwisted root)).color_symm _ _)

theorem residualExact_of_upper (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel)
    (hupper : ResidualUpperExactAt pair root first second) :
    ResidualExactAt pair root first second := by
  intro left right hne
  by_cases hlt : left.val < right.val
  · exact hupper left right hlt
  · have hgt : right.val < left.val := by
      have hle : right.val ≤ left.val := by omega
      have hvalNe : left.val ≠ right.val := by
        exact fun h => hne (Fin.ext h)
      omega
    calc
      reducedCandidateColor pair root first second
          (residualCoordinate pair root first second left)
          (residualCoordinate pair root first second right) =
        reducedCandidateColor pair root first second
          (residualCoordinate pair root first second right)
          (residualCoordinate pair root first second left) :=
            reducedCandidateColor_symm _ _ _ _ _ _
      _ = orderedMatrixColor (reducedLeaf pair root first second)
          right left := hupper right left hgt
      _ = orderedMatrixColor (reducedLeaf pair root first second)
          left right := orderedMatrixColor_symm _ _ _

instance (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) :
    Decidable (ResidualExactAt pair root first second) := by
  unfold ResidualExactAt
  infer_instance

end ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61
end R4333
