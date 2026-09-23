import PricingC.NativeFactorBindSmall240
import PricingC.NativeFactorBindSmall241
import PricingC.NativeFactorBindSmall242
import PricingC.NativeFactorBindSmall243
import PricingC.NativeFactorBindSmall244
import PricingC.NativeFactorBindSmall245
import PricingC.NativeFactorBindSmall246
import PricingC.NativeFactorBindSmall247
import PricingC.NativeFactorBindSmall248
import PricingC.NativeFactorBindSmall249
import PricingC.NativeFactorBindSmall250
import PricingC.NativeFactorBindSmall251
import PricingC.NativeFactorBindSmall252
import PricingC.NativeFactorBindSmall253
import PricingC.NativeFactorBindSmall254
import PricingC.NativeFactorBindSmall255
import PricingC.NativeFactorBindSmall256
import PricingC.NativeFactorBindSmall257
import PricingC.NativeFactorBindSmall258
import PricingC.NativeFactorBindSmall259
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join12 (f:Fin 27280) (hl:24000≤f.val) (hh:f.val<26000):Bind f:=by
 have hlo:240≤f.val/100:=by omega
 have hhi:f.val/100<260:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-24000,by omega⟩
   have h: (⟨24000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small240 j
 · let j:Fin 100:=⟨f.val-24100,by omega⟩
   have h: (⟨24100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small241 j
 · let j:Fin 100:=⟨f.val-24200,by omega⟩
   have h: (⟨24200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small242 j
 · let j:Fin 100:=⟨f.val-24300,by omega⟩
   have h: (⟨24300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small243 j
 · let j:Fin 100:=⟨f.val-24400,by omega⟩
   have h: (⟨24400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small244 j
 · let j:Fin 100:=⟨f.val-24500,by omega⟩
   have h: (⟨24500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small245 j
 · let j:Fin 100:=⟨f.val-24600,by omega⟩
   have h: (⟨24600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small246 j
 · let j:Fin 100:=⟨f.val-24700,by omega⟩
   have h: (⟨24700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small247 j
 · let j:Fin 100:=⟨f.val-24800,by omega⟩
   have h: (⟨24800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small248 j
 · let j:Fin 100:=⟨f.val-24900,by omega⟩
   have h: (⟨24900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small249 j
 · let j:Fin 100:=⟨f.val-25000,by omega⟩
   have h: (⟨25000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small250 j
 · let j:Fin 100:=⟨f.val-25100,by omega⟩
   have h: (⟨25100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small251 j
 · let j:Fin 100:=⟨f.val-25200,by omega⟩
   have h: (⟨25200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small252 j
 · let j:Fin 100:=⟨f.val-25300,by omega⟩
   have h: (⟨25300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small253 j
 · let j:Fin 100:=⟨f.val-25400,by omega⟩
   have h: (⟨25400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small254 j
 · let j:Fin 100:=⟨f.val-25500,by omega⟩
   have h: (⟨25500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small255 j
 · let j:Fin 100:=⟨f.val-25600,by omega⟩
   have h: (⟨25600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small256 j
 · let j:Fin 100:=⟨f.val-25700,by omega⟩
   have h: (⟨25700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small257 j
 · let j:Fin 100:=⟨f.val-25800,by omega⟩
   have h: (⟨25800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small258 j
 · let j:Fin 100:=⟨f.val-25900,by omega⟩
   have h: (⟨25900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small259 j
end PricingC.NativeFactorGeometry
