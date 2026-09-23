import PricingG.CoreCoverConsumer
import PricingC.GIsomorphicComplete
import PricingIntegration.RemainingGComplete

set_option autoImplicit false

namespace PricingIntegration.GComplete
open Ramsey61 Ramsey61.CEncodingCore PricingG

/-- The complete actual-host guarded G exclusion. Both finite case families
are proved by ordinary kernel reductions; no native UNSAT or finite-check
premise occurs. The palette change is one global color permutation. -/
theorem guarded_G_exclusion (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (p q : FourColor) (hG : RegularOverlapGuard c r p q) : False := by
  obtain ⟨σ,_,_,hc',hh⟩ := regular_overlap_supplies_consumer c hc r p q hG
  rcases hh with ⟨x,y,g,phys,hr,hhigh⟩ | ⟨x,d,y,phys,hr,hhigh⟩
  · exact PricingC.GIsomorphic.all_isomorphic_cores_excluded x y g
      (colorRelabel c σ) hc' phys hr hhigh
  · exact PricingIntegration.RemainingGWitnesses.all_remaining_cores_excluded x d y
      (colorRelabel c σ) hc' phys hr hhigh

#print axioms guarded_G_exclusion
end PricingIntegration.GComplete
