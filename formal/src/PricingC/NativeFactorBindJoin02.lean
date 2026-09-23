import PricingC.NativeFactorBindSmall040
import PricingC.NativeFactorBindSmall041
import PricingC.NativeFactorBindSmall042
import PricingC.NativeFactorBindSmall043
import PricingC.NativeFactorBindSmall044
import PricingC.NativeFactorBindSmall045
import PricingC.NativeFactorBindSmall046
import PricingC.NativeFactorBindSmall047
import PricingC.NativeFactorBindSmall048
import PricingC.NativeFactorBindSmall049
import PricingC.NativeFactorBindSmall050
import PricingC.NativeFactorBindSmall051
import PricingC.NativeFactorBindSmall052
import PricingC.NativeFactorBindSmall053
import PricingC.NativeFactorBindSmall054
import PricingC.NativeFactorBindSmall055
import PricingC.NativeFactorBindSmall056
import PricingC.NativeFactorBindSmall057
import PricingC.NativeFactorBindSmall058
import PricingC.NativeFactorBindSmall059
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join02 (f:Fin 27280) (hl:4000≤f.val) (hh:f.val<6000):Bind f:=by
 have hlo:40≤f.val/100:=by omega
 have hhi:f.val/100<60:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-4000,by omega⟩
   have h: (⟨4000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small040 j
 · let j:Fin 100:=⟨f.val-4100,by omega⟩
   have h: (⟨4100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small041 j
 · let j:Fin 100:=⟨f.val-4200,by omega⟩
   have h: (⟨4200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small042 j
 · let j:Fin 100:=⟨f.val-4300,by omega⟩
   have h: (⟨4300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small043 j
 · let j:Fin 100:=⟨f.val-4400,by omega⟩
   have h: (⟨4400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small044 j
 · let j:Fin 100:=⟨f.val-4500,by omega⟩
   have h: (⟨4500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small045 j
 · let j:Fin 100:=⟨f.val-4600,by omega⟩
   have h: (⟨4600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small046 j
 · let j:Fin 100:=⟨f.val-4700,by omega⟩
   have h: (⟨4700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small047 j
 · let j:Fin 100:=⟨f.val-4800,by omega⟩
   have h: (⟨4800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small048 j
 · let j:Fin 100:=⟨f.val-4900,by omega⟩
   have h: (⟨4900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small049 j
 · let j:Fin 100:=⟨f.val-5000,by omega⟩
   have h: (⟨5000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small050 j
 · let j:Fin 100:=⟨f.val-5100,by omega⟩
   have h: (⟨5100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small051 j
 · let j:Fin 100:=⟨f.val-5200,by omega⟩
   have h: (⟨5200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small052 j
 · let j:Fin 100:=⟨f.val-5300,by omega⟩
   have h: (⟨5300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small053 j
 · let j:Fin 100:=⟨f.val-5400,by omega⟩
   have h: (⟨5400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small054 j
 · let j:Fin 100:=⟨f.val-5500,by omega⟩
   have h: (⟨5500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small055 j
 · let j:Fin 100:=⟨f.val-5600,by omega⟩
   have h: (⟨5600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small056 j
 · let j:Fin 100:=⟨f.val-5700,by omega⟩
   have h: (⟨5700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small057 j
 · let j:Fin 100:=⟨f.val-5800,by omega⟩
   have h: (⟨5800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small058 j
 · let j:Fin 100:=⟨f.val-5900,by omega⟩
   have h: (⟨5900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small059 j
end PricingC.NativeFactorGeometry
