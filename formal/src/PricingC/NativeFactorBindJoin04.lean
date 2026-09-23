import PricingC.NativeFactorBindSmall080
import PricingC.NativeFactorBindSmall081
import PricingC.NativeFactorBindSmall082
import PricingC.NativeFactorBindSmall083
import PricingC.NativeFactorBindSmall084
import PricingC.NativeFactorBindSmall085
import PricingC.NativeFactorBindSmall086
import PricingC.NativeFactorBindSmall087
import PricingC.NativeFactorBindSmall088
import PricingC.NativeFactorBindSmall089
import PricingC.NativeFactorBindSmall090
import PricingC.NativeFactorBindSmall091
import PricingC.NativeFactorBindSmall092
import PricingC.NativeFactorBindSmall093
import PricingC.NativeFactorBindSmall094
import PricingC.NativeFactorBindSmall095
import PricingC.NativeFactorBindSmall096
import PricingC.NativeFactorBindSmall097
import PricingC.NativeFactorBindSmall098
import PricingC.NativeFactorBindSmall099
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join04 (f:Fin 27280) (hl:8000≤f.val) (hh:f.val<10000):Bind f:=by
 have hlo:80≤f.val/100:=by omega
 have hhi:f.val/100<100:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-8000,by omega⟩
   have h: (⟨8000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small080 j
 · let j:Fin 100:=⟨f.val-8100,by omega⟩
   have h: (⟨8100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small081 j
 · let j:Fin 100:=⟨f.val-8200,by omega⟩
   have h: (⟨8200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small082 j
 · let j:Fin 100:=⟨f.val-8300,by omega⟩
   have h: (⟨8300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small083 j
 · let j:Fin 100:=⟨f.val-8400,by omega⟩
   have h: (⟨8400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small084 j
 · let j:Fin 100:=⟨f.val-8500,by omega⟩
   have h: (⟨8500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small085 j
 · let j:Fin 100:=⟨f.val-8600,by omega⟩
   have h: (⟨8600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small086 j
 · let j:Fin 100:=⟨f.val-8700,by omega⟩
   have h: (⟨8700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small087 j
 · let j:Fin 100:=⟨f.val-8800,by omega⟩
   have h: (⟨8800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small088 j
 · let j:Fin 100:=⟨f.val-8900,by omega⟩
   have h: (⟨8900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small089 j
 · let j:Fin 100:=⟨f.val-9000,by omega⟩
   have h: (⟨9000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small090 j
 · let j:Fin 100:=⟨f.val-9100,by omega⟩
   have h: (⟨9100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small091 j
 · let j:Fin 100:=⟨f.val-9200,by omega⟩
   have h: (⟨9200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small092 j
 · let j:Fin 100:=⟨f.val-9300,by omega⟩
   have h: (⟨9300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small093 j
 · let j:Fin 100:=⟨f.val-9400,by omega⟩
   have h: (⟨9400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small094 j
 · let j:Fin 100:=⟨f.val-9500,by omega⟩
   have h: (⟨9500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small095 j
 · let j:Fin 100:=⟨f.val-9600,by omega⟩
   have h: (⟨9600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small096 j
 · let j:Fin 100:=⟨f.val-9700,by omega⟩
   have h: (⟨9700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small097 j
 · let j:Fin 100:=⟨f.val-9800,by omega⟩
   have h: (⟨9800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small098 j
 · let j:Fin 100:=⟨f.val-9900,by omega⟩
   have h: (⟨9900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small099 j
end PricingC.NativeFactorGeometry
