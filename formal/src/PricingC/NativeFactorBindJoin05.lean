import PricingC.NativeFactorBindSmall100
import PricingC.NativeFactorBindSmall101
import PricingC.NativeFactorBindSmall102
import PricingC.NativeFactorBindSmall103
import PricingC.NativeFactorBindSmall104
import PricingC.NativeFactorBindSmall105
import PricingC.NativeFactorBindSmall106
import PricingC.NativeFactorBindSmall107
import PricingC.NativeFactorBindSmall108
import PricingC.NativeFactorBindSmall109
import PricingC.NativeFactorBindSmall110
import PricingC.NativeFactorBindSmall111
import PricingC.NativeFactorBindSmall112
import PricingC.NativeFactorBindSmall113
import PricingC.NativeFactorBindSmall114
import PricingC.NativeFactorBindSmall115
import PricingC.NativeFactorBindSmall116
import PricingC.NativeFactorBindSmall117
import PricingC.NativeFactorBindSmall118
import PricingC.NativeFactorBindSmall119
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join05 (f:Fin 27280) (hl:10000≤f.val) (hh:f.val<12000):Bind f:=by
 have hlo:100≤f.val/100:=by omega
 have hhi:f.val/100<120:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-10000,by omega⟩
   have h: (⟨10000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small100 j
 · let j:Fin 100:=⟨f.val-10100,by omega⟩
   have h: (⟨10100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small101 j
 · let j:Fin 100:=⟨f.val-10200,by omega⟩
   have h: (⟨10200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small102 j
 · let j:Fin 100:=⟨f.val-10300,by omega⟩
   have h: (⟨10300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small103 j
 · let j:Fin 100:=⟨f.val-10400,by omega⟩
   have h: (⟨10400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small104 j
 · let j:Fin 100:=⟨f.val-10500,by omega⟩
   have h: (⟨10500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small105 j
 · let j:Fin 100:=⟨f.val-10600,by omega⟩
   have h: (⟨10600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small106 j
 · let j:Fin 100:=⟨f.val-10700,by omega⟩
   have h: (⟨10700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small107 j
 · let j:Fin 100:=⟨f.val-10800,by omega⟩
   have h: (⟨10800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small108 j
 · let j:Fin 100:=⟨f.val-10900,by omega⟩
   have h: (⟨10900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small109 j
 · let j:Fin 100:=⟨f.val-11000,by omega⟩
   have h: (⟨11000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small110 j
 · let j:Fin 100:=⟨f.val-11100,by omega⟩
   have h: (⟨11100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small111 j
 · let j:Fin 100:=⟨f.val-11200,by omega⟩
   have h: (⟨11200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small112 j
 · let j:Fin 100:=⟨f.val-11300,by omega⟩
   have h: (⟨11300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small113 j
 · let j:Fin 100:=⟨f.val-11400,by omega⟩
   have h: (⟨11400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small114 j
 · let j:Fin 100:=⟨f.val-11500,by omega⟩
   have h: (⟨11500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small115 j
 · let j:Fin 100:=⟨f.val-11600,by omega⟩
   have h: (⟨11600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small116 j
 · let j:Fin 100:=⟨f.val-11700,by omega⟩
   have h: (⟨11700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small117 j
 · let j:Fin 100:=⟨f.val-11800,by omega⟩
   have h: (⟨11800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small118 j
 · let j:Fin 100:=⟨f.val-11900,by omega⟩
   have h: (⟨11900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small119 j
end PricingC.NativeFactorGeometry
