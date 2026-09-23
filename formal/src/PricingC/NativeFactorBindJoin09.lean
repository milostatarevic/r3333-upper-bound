import PricingC.NativeFactorBindSmall180
import PricingC.NativeFactorBindSmall181
import PricingC.NativeFactorBindSmall182
import PricingC.NativeFactorBindSmall183
import PricingC.NativeFactorBindSmall184
import PricingC.NativeFactorBindSmall185
import PricingC.NativeFactorBindSmall186
import PricingC.NativeFactorBindSmall187
import PricingC.NativeFactorBindSmall188
import PricingC.NativeFactorBindSmall189
import PricingC.NativeFactorBindSmall190
import PricingC.NativeFactorBindSmall191
import PricingC.NativeFactorBindSmall192
import PricingC.NativeFactorBindSmall193
import PricingC.NativeFactorBindSmall194
import PricingC.NativeFactorBindSmall195
import PricingC.NativeFactorBindSmall196
import PricingC.NativeFactorBindSmall197
import PricingC.NativeFactorBindSmall198
import PricingC.NativeFactorBindSmall199
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join09 (f:Fin 27280) (hl:18000≤f.val) (hh:f.val<20000):Bind f:=by
 have hlo:180≤f.val/100:=by omega
 have hhi:f.val/100<200:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-18000,by omega⟩
   have h: (⟨18000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small180 j
 · let j:Fin 100:=⟨f.val-18100,by omega⟩
   have h: (⟨18100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small181 j
 · let j:Fin 100:=⟨f.val-18200,by omega⟩
   have h: (⟨18200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small182 j
 · let j:Fin 100:=⟨f.val-18300,by omega⟩
   have h: (⟨18300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small183 j
 · let j:Fin 100:=⟨f.val-18400,by omega⟩
   have h: (⟨18400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small184 j
 · let j:Fin 100:=⟨f.val-18500,by omega⟩
   have h: (⟨18500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small185 j
 · let j:Fin 100:=⟨f.val-18600,by omega⟩
   have h: (⟨18600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small186 j
 · let j:Fin 100:=⟨f.val-18700,by omega⟩
   have h: (⟨18700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small187 j
 · let j:Fin 100:=⟨f.val-18800,by omega⟩
   have h: (⟨18800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small188 j
 · let j:Fin 100:=⟨f.val-18900,by omega⟩
   have h: (⟨18900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small189 j
 · let j:Fin 100:=⟨f.val-19000,by omega⟩
   have h: (⟨19000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small190 j
 · let j:Fin 100:=⟨f.val-19100,by omega⟩
   have h: (⟨19100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small191 j
 · let j:Fin 100:=⟨f.val-19200,by omega⟩
   have h: (⟨19200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small192 j
 · let j:Fin 100:=⟨f.val-19300,by omega⟩
   have h: (⟨19300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small193 j
 · let j:Fin 100:=⟨f.val-19400,by omega⟩
   have h: (⟨19400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small194 j
 · let j:Fin 100:=⟨f.val-19500,by omega⟩
   have h: (⟨19500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small195 j
 · let j:Fin 100:=⟨f.val-19600,by omega⟩
   have h: (⟨19600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small196 j
 · let j:Fin 100:=⟨f.val-19700,by omega⟩
   have h: (⟨19700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small197 j
 · let j:Fin 100:=⟨f.val-19800,by omega⟩
   have h: (⟨19800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small198 j
 · let j:Fin 100:=⟨f.val-19900,by omega⟩
   have h: (⟨19900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small199 j
end PricingC.NativeFactorGeometry
