import PricingC.NativeFactorBindSmall020
import PricingC.NativeFactorBindSmall021
import PricingC.NativeFactorBindSmall022
import PricingC.NativeFactorBindSmall023
import PricingC.NativeFactorBindSmall024
import PricingC.NativeFactorBindSmall025
import PricingC.NativeFactorBindSmall026
import PricingC.NativeFactorBindSmall027
import PricingC.NativeFactorBindSmall028
import PricingC.NativeFactorBindSmall029
import PricingC.NativeFactorBindSmall030
import PricingC.NativeFactorBindSmall031
import PricingC.NativeFactorBindSmall032
import PricingC.NativeFactorBindSmall033
import PricingC.NativeFactorBindSmall034
import PricingC.NativeFactorBindSmall035
import PricingC.NativeFactorBindSmall036
import PricingC.NativeFactorBindSmall037
import PricingC.NativeFactorBindSmall038
import PricingC.NativeFactorBindSmall039
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join01 (f:Fin 27280) (hl:2000≤f.val) (hh:f.val<4000):Bind f:=by
 have hlo:20≤f.val/100:=by omega
 have hhi:f.val/100<40:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-2000,by omega⟩
   have h: (⟨2000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small020 j
 · let j:Fin 100:=⟨f.val-2100,by omega⟩
   have h: (⟨2100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small021 j
 · let j:Fin 100:=⟨f.val-2200,by omega⟩
   have h: (⟨2200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small022 j
 · let j:Fin 100:=⟨f.val-2300,by omega⟩
   have h: (⟨2300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small023 j
 · let j:Fin 100:=⟨f.val-2400,by omega⟩
   have h: (⟨2400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small024 j
 · let j:Fin 100:=⟨f.val-2500,by omega⟩
   have h: (⟨2500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small025 j
 · let j:Fin 100:=⟨f.val-2600,by omega⟩
   have h: (⟨2600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small026 j
 · let j:Fin 100:=⟨f.val-2700,by omega⟩
   have h: (⟨2700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small027 j
 · let j:Fin 100:=⟨f.val-2800,by omega⟩
   have h: (⟨2800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small028 j
 · let j:Fin 100:=⟨f.val-2900,by omega⟩
   have h: (⟨2900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small029 j
 · let j:Fin 100:=⟨f.val-3000,by omega⟩
   have h: (⟨3000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small030 j
 · let j:Fin 100:=⟨f.val-3100,by omega⟩
   have h: (⟨3100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small031 j
 · let j:Fin 100:=⟨f.val-3200,by omega⟩
   have h: (⟨3200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small032 j
 · let j:Fin 100:=⟨f.val-3300,by omega⟩
   have h: (⟨3300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small033 j
 · let j:Fin 100:=⟨f.val-3400,by omega⟩
   have h: (⟨3400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small034 j
 · let j:Fin 100:=⟨f.val-3500,by omega⟩
   have h: (⟨3500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small035 j
 · let j:Fin 100:=⟨f.val-3600,by omega⟩
   have h: (⟨3600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small036 j
 · let j:Fin 100:=⟨f.val-3700,by omega⟩
   have h: (⟨3700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small037 j
 · let j:Fin 100:=⟨f.val-3800,by omega⟩
   have h: (⟨3800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small038 j
 · let j:Fin 100:=⟨f.val-3900,by omega⟩
   have h: (⟨3900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small039 j
end PricingC.NativeFactorGeometry
