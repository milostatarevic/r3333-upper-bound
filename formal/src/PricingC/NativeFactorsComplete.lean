import PricingC.NativeFactorGeometryComplete
import PricingC.NativeFactorGeometryTransport
import PricingC.NativeFactorBindJoin00
import PricingC.NativeFactorBindJoin01
import PricingC.NativeFactorBindJoin02
import PricingC.NativeFactorBindJoin03
import PricingC.NativeFactorBindJoin04
import PricingC.NativeFactorBindJoin05
import PricingC.NativeFactorBindJoin06
import PricingC.NativeFactorBindJoin07
import PricingC.NativeFactorBindJoin08
import PricingC.NativeFactorBindJoin09
import PricingC.NativeFactorBindJoin10
import PricingC.NativeFactorBindJoin11
import PricingC.NativeFactorBindJoin12
import PricingC.NativeFactorBindJoin13
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind Good geometryOf
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_factor_bind (f:Fin 27280):Bind f:=by
 have hq:f.val/2000<14:=by omega
 interval_cases heq:f.val/2000
 · exact bind_join00 f (by omega) (by omega)
 · exact bind_join01 f (by omega) (by omega)
 · exact bind_join02 f (by omega) (by omega)
 · exact bind_join03 f (by omega) (by omega)
 · exact bind_join04 f (by omega) (by omega)
 · exact bind_join05 f (by omega) (by omega)
 · exact bind_join06 f (by omega) (by omega)
 · exact bind_join07 f (by omega) (by omega)
 · exact bind_join08 f (by omega) (by omega)
 · exact bind_join09 f (by omega) (by omega)
 · exact bind_join10 f (by omega) (by omega)
 · exact bind_join11 f (by omega) (by omega)
 · exact bind_join12 f (by omega) (by omega)
 · exact bind_join13 f (by omega) (by omega)
theorem all_factor_valid (f:Fin 27280):NativeActionFactors.Valid f:=
 valid_of_bind f (all_geometry_good (geometryOf f)) (all_factor_bind f)
#print axioms all_factor_valid
end PricingC.NativeFactorGeometry
