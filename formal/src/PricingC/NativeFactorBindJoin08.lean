import PricingC.NativeFactorBindSmall160
import PricingC.NativeFactorBindSmall161
import PricingC.NativeFactorBindSmall162
import PricingC.NativeFactorBindSmall163
import PricingC.NativeFactorBindSmall164
import PricingC.NativeFactorBindSmall165
import PricingC.NativeFactorBindSmall166
import PricingC.NativeFactorBindSmall167
import PricingC.NativeFactorBindSmall168
import PricingC.NativeFactorBindSmall169
import PricingC.NativeFactorBindSmall170
import PricingC.NativeFactorBindSmall171
import PricingC.NativeFactorBindSmall172
import PricingC.NativeFactorBindSmall173
import PricingC.NativeFactorBindSmall174
import PricingC.NativeFactorBindSmall175
import PricingC.NativeFactorBindSmall176
import PricingC.NativeFactorBindSmall177
import PricingC.NativeFactorBindSmall178
import PricingC.NativeFactorBindSmall179
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join08 (f:Fin 27280) (hl:16000≤f.val) (hh:f.val<18000):Bind f:=by
 have hlo:160≤f.val/100:=by omega
 have hhi:f.val/100<180:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-16000,by omega⟩
   have h: (⟨16000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small160 j
 · let j:Fin 100:=⟨f.val-16100,by omega⟩
   have h: (⟨16100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small161 j
 · let j:Fin 100:=⟨f.val-16200,by omega⟩
   have h: (⟨16200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small162 j
 · let j:Fin 100:=⟨f.val-16300,by omega⟩
   have h: (⟨16300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small163 j
 · let j:Fin 100:=⟨f.val-16400,by omega⟩
   have h: (⟨16400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small164 j
 · let j:Fin 100:=⟨f.val-16500,by omega⟩
   have h: (⟨16500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small165 j
 · let j:Fin 100:=⟨f.val-16600,by omega⟩
   have h: (⟨16600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small166 j
 · let j:Fin 100:=⟨f.val-16700,by omega⟩
   have h: (⟨16700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small167 j
 · let j:Fin 100:=⟨f.val-16800,by omega⟩
   have h: (⟨16800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small168 j
 · let j:Fin 100:=⟨f.val-16900,by omega⟩
   have h: (⟨16900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small169 j
 · let j:Fin 100:=⟨f.val-17000,by omega⟩
   have h: (⟨17000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small170 j
 · let j:Fin 100:=⟨f.val-17100,by omega⟩
   have h: (⟨17100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small171 j
 · let j:Fin 100:=⟨f.val-17200,by omega⟩
   have h: (⟨17200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small172 j
 · let j:Fin 100:=⟨f.val-17300,by omega⟩
   have h: (⟨17300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small173 j
 · let j:Fin 100:=⟨f.val-17400,by omega⟩
   have h: (⟨17400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small174 j
 · let j:Fin 100:=⟨f.val-17500,by omega⟩
   have h: (⟨17500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small175 j
 · let j:Fin 100:=⟨f.val-17600,by omega⟩
   have h: (⟨17600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small176 j
 · let j:Fin 100:=⟨f.val-17700,by omega⟩
   have h: (⟨17700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small177 j
 · let j:Fin 100:=⟨f.val-17800,by omega⟩
   have h: (⟨17800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small178 j
 · let j:Fin 100:=⟨f.val-17900,by omega⟩
   have h: (⟨17900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small179 j
end PricingC.NativeFactorGeometry
