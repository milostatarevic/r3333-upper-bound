import PricingC.NativeFactorGeometryData
namespace PricingC.NativeFactorGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem geometry_small09:∀j:Fin 100,Good ⟨900+j.val,by omega⟩:=by decide +kernel
end PricingC.NativeFactorGeometry
