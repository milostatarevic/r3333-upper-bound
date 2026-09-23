import PricingIntegration.GCoreConsumer
import PricingIntegration.RemainingGFastCore

namespace PricingIntegration.RemainingGWitnesses
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.GCoreConsumer

def Rejected (b : CoreBase) : Prop := ∀ (c : Host), NoMonochromaticTriangle c →
    ∀ (phys : Fin 33 ↪ Vertex), Realizes c phys b → High c phys → False

end PricingIntegration.RemainingGWitnesses
