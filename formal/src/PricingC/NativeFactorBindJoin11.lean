import PricingC.NativeFactorBindSmall220
import PricingC.NativeFactorBindSmall221
import PricingC.NativeFactorBindSmall222
import PricingC.NativeFactorBindSmall223
import PricingC.NativeFactorBindSmall224
import PricingC.NativeFactorBindSmall225
import PricingC.NativeFactorBindSmall226
import PricingC.NativeFactorBindSmall227
import PricingC.NativeFactorBindSmall228
import PricingC.NativeFactorBindSmall229
import PricingC.NativeFactorBindSmall230
import PricingC.NativeFactorBindSmall231
import PricingC.NativeFactorBindSmall232
import PricingC.NativeFactorBindSmall233
import PricingC.NativeFactorBindSmall234
import PricingC.NativeFactorBindSmall235
import PricingC.NativeFactorBindSmall236
import PricingC.NativeFactorBindSmall237
import PricingC.NativeFactorBindSmall238
import PricingC.NativeFactorBindSmall239
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join11 (f:Fin 27280) (hl:22000≤f.val) (hh:f.val<24000):Bind f:=by
 have hlo:220≤f.val/100:=by omega
 have hhi:f.val/100<240:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-22000,by omega⟩
   have h: (⟨22000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small220 j
 · let j:Fin 100:=⟨f.val-22100,by omega⟩
   have h: (⟨22100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small221 j
 · let j:Fin 100:=⟨f.val-22200,by omega⟩
   have h: (⟨22200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small222 j
 · let j:Fin 100:=⟨f.val-22300,by omega⟩
   have h: (⟨22300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small223 j
 · let j:Fin 100:=⟨f.val-22400,by omega⟩
   have h: (⟨22400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small224 j
 · let j:Fin 100:=⟨f.val-22500,by omega⟩
   have h: (⟨22500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small225 j
 · let j:Fin 100:=⟨f.val-22600,by omega⟩
   have h: (⟨22600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small226 j
 · let j:Fin 100:=⟨f.val-22700,by omega⟩
   have h: (⟨22700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small227 j
 · let j:Fin 100:=⟨f.val-22800,by omega⟩
   have h: (⟨22800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small228 j
 · let j:Fin 100:=⟨f.val-22900,by omega⟩
   have h: (⟨22900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small229 j
 · let j:Fin 100:=⟨f.val-23000,by omega⟩
   have h: (⟨23000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small230 j
 · let j:Fin 100:=⟨f.val-23100,by omega⟩
   have h: (⟨23100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small231 j
 · let j:Fin 100:=⟨f.val-23200,by omega⟩
   have h: (⟨23200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small232 j
 · let j:Fin 100:=⟨f.val-23300,by omega⟩
   have h: (⟨23300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small233 j
 · let j:Fin 100:=⟨f.val-23400,by omega⟩
   have h: (⟨23400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small234 j
 · let j:Fin 100:=⟨f.val-23500,by omega⟩
   have h: (⟨23500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small235 j
 · let j:Fin 100:=⟨f.val-23600,by omega⟩
   have h: (⟨23600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small236 j
 · let j:Fin 100:=⟨f.val-23700,by omega⟩
   have h: (⟨23700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small237 j
 · let j:Fin 100:=⟨f.val-23800,by omega⟩
   have h: (⟨23800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small238 j
 · let j:Fin 100:=⟨f.val-23900,by omega⟩
   have h: (⟨23900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small239 j
end PricingC.NativeFactorGeometry
