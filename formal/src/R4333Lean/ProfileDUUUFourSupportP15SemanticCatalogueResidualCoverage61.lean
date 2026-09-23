import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair061
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair161
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair261
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair361
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair461
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair561
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair661
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair761
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualPair861

/-!
# Complete residual coverage for the factorized P15 semantic catalogue

The expensive upper-triangle checks are cached in nine support-pair modules.
This file only dispatches between them and restores the directed edge form.
-/

namespace R4333
namespace ProfileDUUUFourSupportP15SemanticCatalogueResidualCoverage61

open ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair061
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair161
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair261
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair361
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair461
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair561
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair661
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair761
open ProfileDUUUFourSupportP15SemanticCatalogueResidualPair861

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem residualExact (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) :
    ResidualExactAt pair root first second := by
  fin_cases pair
  · exact residualExact_pair0 root first second
  · exact residualExact_pair1 root first second
  · exact residualExact_pair2 root first second
  · exact residualExact_pair3 root first second
  · exact residualExact_pair4 root first second
  · exact residualExact_pair5 root first second
  · exact residualExact_pair6 root first second
  · exact residualExact_pair7 root first second
  · exact residualExact_pair8 root first second

/-- Every one of the 2,250 reduced rooted labelings is exactly a stored
ordered leaf after its generated, checked local coordinate action. -/
theorem reducedLeaf_exact (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) (left right : Fin 14)
    (hne : left ≠ right) :
    ProfileDUUUFourSupportP15SemanticCatalogueFinite61.reducedCandidateColor
        pair root first second
        (residualCoordinate pair root first second left)
        (residualCoordinate pair root first second right) =
      ProfileDUUUFourSupportP15SwapFiniteCoverage61.orderedMatrixColor
        (ProfileDUUUFourSupportP15SemanticCatalogueData61.reducedLeaf
          pair root first second) left right := by
  exact residualExact pair root first second left right hne

#print axioms residualExact
#print axioms reducedLeaf_exact

end ProfileDUUUFourSupportP15SemanticCatalogueResidualCoverage61
end R4333
