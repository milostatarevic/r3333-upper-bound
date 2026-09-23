import PricingC.NativeFactorBindSmall060
import PricingC.NativeFactorBindSmall061
import PricingC.NativeFactorBindSmall062
import PricingC.NativeFactorBindSmall063
import PricingC.NativeFactorBindSmall064
import PricingC.NativeFactorBindSmall065
import PricingC.NativeFactorBindSmall066
import PricingC.NativeFactorBindSmall067
import PricingC.NativeFactorBindSmall068
import PricingC.NativeFactorBindSmall069
import PricingC.NativeFactorBindSmall070
import PricingC.NativeFactorBindSmall071
import PricingC.NativeFactorBindSmall072
import PricingC.NativeFactorBindSmall073
import PricingC.NativeFactorBindSmall074
import PricingC.NativeFactorBindSmall075
import PricingC.NativeFactorBindSmall076
import PricingC.NativeFactorBindSmall077
import PricingC.NativeFactorBindSmall078
import PricingC.NativeFactorBindSmall079
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join03 (f:Fin 27280) (hl:6000≤f.val) (hh:f.val<8000):Bind f:=by
 have hlo:60≤f.val/100:=by omega
 have hhi:f.val/100<80:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-6000,by omega⟩
   have h: (⟨6000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small060 j
 · let j:Fin 100:=⟨f.val-6100,by omega⟩
   have h: (⟨6100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small061 j
 · let j:Fin 100:=⟨f.val-6200,by omega⟩
   have h: (⟨6200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small062 j
 · let j:Fin 100:=⟨f.val-6300,by omega⟩
   have h: (⟨6300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small063 j
 · let j:Fin 100:=⟨f.val-6400,by omega⟩
   have h: (⟨6400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small064 j
 · let j:Fin 100:=⟨f.val-6500,by omega⟩
   have h: (⟨6500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small065 j
 · let j:Fin 100:=⟨f.val-6600,by omega⟩
   have h: (⟨6600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small066 j
 · let j:Fin 100:=⟨f.val-6700,by omega⟩
   have h: (⟨6700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small067 j
 · let j:Fin 100:=⟨f.val-6800,by omega⟩
   have h: (⟨6800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small068 j
 · let j:Fin 100:=⟨f.val-6900,by omega⟩
   have h: (⟨6900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small069 j
 · let j:Fin 100:=⟨f.val-7000,by omega⟩
   have h: (⟨7000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small070 j
 · let j:Fin 100:=⟨f.val-7100,by omega⟩
   have h: (⟨7100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small071 j
 · let j:Fin 100:=⟨f.val-7200,by omega⟩
   have h: (⟨7200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small072 j
 · let j:Fin 100:=⟨f.val-7300,by omega⟩
   have h: (⟨7300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small073 j
 · let j:Fin 100:=⟨f.val-7400,by omega⟩
   have h: (⟨7400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small074 j
 · let j:Fin 100:=⟨f.val-7500,by omega⟩
   have h: (⟨7500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small075 j
 · let j:Fin 100:=⟨f.val-7600,by omega⟩
   have h: (⟨7600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small076 j
 · let j:Fin 100:=⟨f.val-7700,by omega⟩
   have h: (⟨7700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small077 j
 · let j:Fin 100:=⟨f.val-7800,by omega⟩
   have h: (⟨7800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small078 j
 · let j:Fin 100:=⟨f.val-7900,by omega⟩
   have h: (⟨7900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small079 j
end PricingC.NativeFactorGeometry
