import PricingIntegration.GCoreConsumer
import PricingC.GLayoutSkeleton

namespace PricingC.GIsomorphic
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.GCoreConsumer

def CoreExcluded (base : CoreBase) : Prop :=
 ∀ (c : Host),NoMonochromaticTriangle c → ∀ (phys : Fin 33 ↪ Vertex),
 Realizes c phys base → High c phys → False

def blockCase (b : Fin 36) (i : Fin 100) : Fin 3600 := ⟨b.val*100+i.val,by omega⟩
end PricingC.GIsomorphic
