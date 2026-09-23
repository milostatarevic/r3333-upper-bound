import PricingC.NativeFactorGeometryData
namespace PricingC.NativeFactorGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem bind_small095:∀j:Fin 100,Bind ⟨9500+j.val,by omega⟩:=by decide +kernel
end PricingC.NativeFactorGeometry
