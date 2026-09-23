import PricingC.NativeFactorGeometryData
namespace PricingC.NativeFactorGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem geometry_small13:∀j:Fin 90,Good ⟨1300+j.val,by omega⟩:=by decide +kernel
end PricingC.NativeFactorGeometry
