import PricingC.NativeFactorBindSmall120
import PricingC.NativeFactorBindSmall121
import PricingC.NativeFactorBindSmall122
import PricingC.NativeFactorBindSmall123
import PricingC.NativeFactorBindSmall124
import PricingC.NativeFactorBindSmall125
import PricingC.NativeFactorBindSmall126
import PricingC.NativeFactorBindSmall127
import PricingC.NativeFactorBindSmall128
import PricingC.NativeFactorBindSmall129
import PricingC.NativeFactorBindSmall130
import PricingC.NativeFactorBindSmall131
import PricingC.NativeFactorBindSmall132
import PricingC.NativeFactorBindSmall133
import PricingC.NativeFactorBindSmall134
import PricingC.NativeFactorBindSmall135
import PricingC.NativeFactorBindSmall136
import PricingC.NativeFactorBindSmall137
import PricingC.NativeFactorBindSmall138
import PricingC.NativeFactorBindSmall139
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join06 (f:Fin 27280) (hl:12000≤f.val) (hh:f.val<14000):Bind f:=by
 have hlo:120≤f.val/100:=by omega
 have hhi:f.val/100<140:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-12000,by omega⟩
   have h: (⟨12000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small120 j
 · let j:Fin 100:=⟨f.val-12100,by omega⟩
   have h: (⟨12100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small121 j
 · let j:Fin 100:=⟨f.val-12200,by omega⟩
   have h: (⟨12200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small122 j
 · let j:Fin 100:=⟨f.val-12300,by omega⟩
   have h: (⟨12300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small123 j
 · let j:Fin 100:=⟨f.val-12400,by omega⟩
   have h: (⟨12400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small124 j
 · let j:Fin 100:=⟨f.val-12500,by omega⟩
   have h: (⟨12500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small125 j
 · let j:Fin 100:=⟨f.val-12600,by omega⟩
   have h: (⟨12600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small126 j
 · let j:Fin 100:=⟨f.val-12700,by omega⟩
   have h: (⟨12700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small127 j
 · let j:Fin 100:=⟨f.val-12800,by omega⟩
   have h: (⟨12800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small128 j
 · let j:Fin 100:=⟨f.val-12900,by omega⟩
   have h: (⟨12900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small129 j
 · let j:Fin 100:=⟨f.val-13000,by omega⟩
   have h: (⟨13000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small130 j
 · let j:Fin 100:=⟨f.val-13100,by omega⟩
   have h: (⟨13100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small131 j
 · let j:Fin 100:=⟨f.val-13200,by omega⟩
   have h: (⟨13200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small132 j
 · let j:Fin 100:=⟨f.val-13300,by omega⟩
   have h: (⟨13300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small133 j
 · let j:Fin 100:=⟨f.val-13400,by omega⟩
   have h: (⟨13400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small134 j
 · let j:Fin 100:=⟨f.val-13500,by omega⟩
   have h: (⟨13500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small135 j
 · let j:Fin 100:=⟨f.val-13600,by omega⟩
   have h: (⟨13600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small136 j
 · let j:Fin 100:=⟨f.val-13700,by omega⟩
   have h: (⟨13700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small137 j
 · let j:Fin 100:=⟨f.val-13800,by omega⟩
   have h: (⟨13800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small138 j
 · let j:Fin 100:=⟨f.val-13900,by omega⟩
   have h: (⟨13900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small139 j
end PricingC.NativeFactorGeometry
