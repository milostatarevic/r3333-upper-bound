import PricingC.NativeFactorBindSmall200
import PricingC.NativeFactorBindSmall201
import PricingC.NativeFactorBindSmall202
import PricingC.NativeFactorBindSmall203
import PricingC.NativeFactorBindSmall204
import PricingC.NativeFactorBindSmall205
import PricingC.NativeFactorBindSmall206
import PricingC.NativeFactorBindSmall207
import PricingC.NativeFactorBindSmall208
import PricingC.NativeFactorBindSmall209
import PricingC.NativeFactorBindSmall210
import PricingC.NativeFactorBindSmall211
import PricingC.NativeFactorBindSmall212
import PricingC.NativeFactorBindSmall213
import PricingC.NativeFactorBindSmall214
import PricingC.NativeFactorBindSmall215
import PricingC.NativeFactorBindSmall216
import PricingC.NativeFactorBindSmall217
import PricingC.NativeFactorBindSmall218
import PricingC.NativeFactorBindSmall219
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join10 (f:Fin 27280) (hl:20000≤f.val) (hh:f.val<22000):Bind f:=by
 have hlo:200≤f.val/100:=by omega
 have hhi:f.val/100<220:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-20000,by omega⟩
   have h: (⟨20000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small200 j
 · let j:Fin 100:=⟨f.val-20100,by omega⟩
   have h: (⟨20100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small201 j
 · let j:Fin 100:=⟨f.val-20200,by omega⟩
   have h: (⟨20200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small202 j
 · let j:Fin 100:=⟨f.val-20300,by omega⟩
   have h: (⟨20300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small203 j
 · let j:Fin 100:=⟨f.val-20400,by omega⟩
   have h: (⟨20400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small204 j
 · let j:Fin 100:=⟨f.val-20500,by omega⟩
   have h: (⟨20500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small205 j
 · let j:Fin 100:=⟨f.val-20600,by omega⟩
   have h: (⟨20600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small206 j
 · let j:Fin 100:=⟨f.val-20700,by omega⟩
   have h: (⟨20700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small207 j
 · let j:Fin 100:=⟨f.val-20800,by omega⟩
   have h: (⟨20800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small208 j
 · let j:Fin 100:=⟨f.val-20900,by omega⟩
   have h: (⟨20900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small209 j
 · let j:Fin 100:=⟨f.val-21000,by omega⟩
   have h: (⟨21000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small210 j
 · let j:Fin 100:=⟨f.val-21100,by omega⟩
   have h: (⟨21100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small211 j
 · let j:Fin 100:=⟨f.val-21200,by omega⟩
   have h: (⟨21200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small212 j
 · let j:Fin 100:=⟨f.val-21300,by omega⟩
   have h: (⟨21300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small213 j
 · let j:Fin 100:=⟨f.val-21400,by omega⟩
   have h: (⟨21400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small214 j
 · let j:Fin 100:=⟨f.val-21500,by omega⟩
   have h: (⟨21500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small215 j
 · let j:Fin 100:=⟨f.val-21600,by omega⟩
   have h: (⟨21600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small216 j
 · let j:Fin 100:=⟨f.val-21700,by omega⟩
   have h: (⟨21700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small217 j
 · let j:Fin 100:=⟨f.val-21800,by omega⟩
   have h: (⟨21800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small218 j
 · let j:Fin 100:=⟨f.val-21900,by omega⟩
   have h: (⟨21900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small219 j
end PricingC.NativeFactorGeometry
