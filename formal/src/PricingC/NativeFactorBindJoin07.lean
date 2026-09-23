import PricingC.NativeFactorBindSmall140
import PricingC.NativeFactorBindSmall141
import PricingC.NativeFactorBindSmall142
import PricingC.NativeFactorBindSmall143
import PricingC.NativeFactorBindSmall144
import PricingC.NativeFactorBindSmall145
import PricingC.NativeFactorBindSmall146
import PricingC.NativeFactorBindSmall147
import PricingC.NativeFactorBindSmall148
import PricingC.NativeFactorBindSmall149
import PricingC.NativeFactorBindSmall150
import PricingC.NativeFactorBindSmall151
import PricingC.NativeFactorBindSmall152
import PricingC.NativeFactorBindSmall153
import PricingC.NativeFactorBindSmall154
import PricingC.NativeFactorBindSmall155
import PricingC.NativeFactorBindSmall156
import PricingC.NativeFactorBindSmall157
import PricingC.NativeFactorBindSmall158
import PricingC.NativeFactorBindSmall159
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join07 (f:Fin 27280) (hl:14000≤f.val) (hh:f.val<16000):Bind f:=by
 have hlo:140≤f.val/100:=by omega
 have hhi:f.val/100<160:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-14000,by omega⟩
   have h: (⟨14000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small140 j
 · let j:Fin 100:=⟨f.val-14100,by omega⟩
   have h: (⟨14100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small141 j
 · let j:Fin 100:=⟨f.val-14200,by omega⟩
   have h: (⟨14200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small142 j
 · let j:Fin 100:=⟨f.val-14300,by omega⟩
   have h: (⟨14300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small143 j
 · let j:Fin 100:=⟨f.val-14400,by omega⟩
   have h: (⟨14400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small144 j
 · let j:Fin 100:=⟨f.val-14500,by omega⟩
   have h: (⟨14500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small145 j
 · let j:Fin 100:=⟨f.val-14600,by omega⟩
   have h: (⟨14600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small146 j
 · let j:Fin 100:=⟨f.val-14700,by omega⟩
   have h: (⟨14700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small147 j
 · let j:Fin 100:=⟨f.val-14800,by omega⟩
   have h: (⟨14800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small148 j
 · let j:Fin 100:=⟨f.val-14900,by omega⟩
   have h: (⟨14900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small149 j
 · let j:Fin 100:=⟨f.val-15000,by omega⟩
   have h: (⟨15000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small150 j
 · let j:Fin 100:=⟨f.val-15100,by omega⟩
   have h: (⟨15100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small151 j
 · let j:Fin 100:=⟨f.val-15200,by omega⟩
   have h: (⟨15200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small152 j
 · let j:Fin 100:=⟨f.val-15300,by omega⟩
   have h: (⟨15300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small153 j
 · let j:Fin 100:=⟨f.val-15400,by omega⟩
   have h: (⟨15400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small154 j
 · let j:Fin 100:=⟨f.val-15500,by omega⟩
   have h: (⟨15500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small155 j
 · let j:Fin 100:=⟨f.val-15600,by omega⟩
   have h: (⟨15600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small156 j
 · let j:Fin 100:=⟨f.val-15700,by omega⟩
   have h: (⟨15700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small157 j
 · let j:Fin 100:=⟨f.val-15800,by omega⟩
   have h: (⟨15800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small158 j
 · let j:Fin 100:=⟨f.val-15900,by omega⟩
   have h: (⟨15900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small159 j
end PricingC.NativeFactorGeometry
