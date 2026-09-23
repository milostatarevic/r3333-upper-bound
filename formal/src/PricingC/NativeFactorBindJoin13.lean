import PricingC.NativeFactorBindSmall260
import PricingC.NativeFactorBindSmall261
import PricingC.NativeFactorBindSmall262
import PricingC.NativeFactorBindSmall263
import PricingC.NativeFactorBindSmall264
import PricingC.NativeFactorBindSmall265
import PricingC.NativeFactorBindSmall266
import PricingC.NativeFactorBindSmall267
import PricingC.NativeFactorBindSmall268
import PricingC.NativeFactorBindSmall269
import PricingC.NativeFactorBindSmall270
import PricingC.NativeFactorBindSmall271
import PricingC.NativeFactorBindSmall272
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join13 (f:Fin 27280) (hl:26000≤f.val) (hh:f.val<27280):Bind f:=by
 have hlo:260≤f.val/100:=by omega
 have hhi:f.val/100<273:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-26000,by omega⟩
   have h: (⟨26000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small260 j
 · let j:Fin 100:=⟨f.val-26100,by omega⟩
   have h: (⟨26100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small261 j
 · let j:Fin 100:=⟨f.val-26200,by omega⟩
   have h: (⟨26200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small262 j
 · let j:Fin 100:=⟨f.val-26300,by omega⟩
   have h: (⟨26300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small263 j
 · let j:Fin 100:=⟨f.val-26400,by omega⟩
   have h: (⟨26400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small264 j
 · let j:Fin 100:=⟨f.val-26500,by omega⟩
   have h: (⟨26500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small265 j
 · let j:Fin 100:=⟨f.val-26600,by omega⟩
   have h: (⟨26600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small266 j
 · let j:Fin 100:=⟨f.val-26700,by omega⟩
   have h: (⟨26700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small267 j
 · let j:Fin 100:=⟨f.val-26800,by omega⟩
   have h: (⟨26800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small268 j
 · let j:Fin 100:=⟨f.val-26900,by omega⟩
   have h: (⟨26900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small269 j
 · let j:Fin 100:=⟨f.val-27000,by omega⟩
   have h: (⟨27000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small270 j
 · let j:Fin 100:=⟨f.val-27100,by omega⟩
   have h: (⟨27100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small271 j
 · let j:Fin 80:=⟨f.val-27200,by omega⟩
   have h: (⟨27200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small272 j
end PricingC.NativeFactorGeometry
