import PricingC.NativeFactorGeometryData
namespace PricingC.NativeFactorGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem bind_small250:∀j:Fin 100,Bind ⟨25000+j.val,by omega⟩:=by decide +kernel
end PricingC.NativeFactorGeometry
