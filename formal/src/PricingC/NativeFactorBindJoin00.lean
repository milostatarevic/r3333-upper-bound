import PricingC.NativeFactorBindSmall000
import PricingC.NativeFactorBindSmall001
import PricingC.NativeFactorBindSmall002
import PricingC.NativeFactorBindSmall003
import PricingC.NativeFactorBindSmall004
import PricingC.NativeFactorBindSmall005
import PricingC.NativeFactorBindSmall006
import PricingC.NativeFactorBindSmall007
import PricingC.NativeFactorBindSmall008
import PricingC.NativeFactorBindSmall009
import PricingC.NativeFactorBindSmall010
import PricingC.NativeFactorBindSmall011
import PricingC.NativeFactorBindSmall012
import PricingC.NativeFactorBindSmall013
import PricingC.NativeFactorBindSmall014
import PricingC.NativeFactorBindSmall015
import PricingC.NativeFactorBindSmall016
import PricingC.NativeFactorBindSmall017
import PricingC.NativeFactorBindSmall018
import PricingC.NativeFactorBindSmall019
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Bind
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem bind_join00 (f:Fin 27280) (hl:0≤f.val) (hh:f.val<2000):Bind f:=by
 have hlo:0≤f.val/100:=by omega
 have hhi:f.val/100<20:=by omega
 interval_cases heq:f.val/100
 · let j:Fin 100:=⟨f.val-0,by omega⟩
   have h: (⟨0+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small000 j
 · let j:Fin 100:=⟨f.val-100,by omega⟩
   have h: (⟨100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small001 j
 · let j:Fin 100:=⟨f.val-200,by omega⟩
   have h: (⟨200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small002 j
 · let j:Fin 100:=⟨f.val-300,by omega⟩
   have h: (⟨300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small003 j
 · let j:Fin 100:=⟨f.val-400,by omega⟩
   have h: (⟨400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small004 j
 · let j:Fin 100:=⟨f.val-500,by omega⟩
   have h: (⟨500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small005 j
 · let j:Fin 100:=⟨f.val-600,by omega⟩
   have h: (⟨600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small006 j
 · let j:Fin 100:=⟨f.val-700,by omega⟩
   have h: (⟨700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small007 j
 · let j:Fin 100:=⟨f.val-800,by omega⟩
   have h: (⟨800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small008 j
 · let j:Fin 100:=⟨f.val-900,by omega⟩
   have h: (⟨900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small009 j
 · let j:Fin 100:=⟨f.val-1000,by omega⟩
   have h: (⟨1000+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small010 j
 · let j:Fin 100:=⟨f.val-1100,by omega⟩
   have h: (⟨1100+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small011 j
 · let j:Fin 100:=⟨f.val-1200,by omega⟩
   have h: (⟨1200+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small012 j
 · let j:Fin 100:=⟨f.val-1300,by omega⟩
   have h: (⟨1300+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small013 j
 · let j:Fin 100:=⟨f.val-1400,by omega⟩
   have h: (⟨1400+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small014 j
 · let j:Fin 100:=⟨f.val-1500,by omega⟩
   have h: (⟨1500+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small015 j
 · let j:Fin 100:=⟨f.val-1600,by omega⟩
   have h: (⟨1600+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small016 j
 · let j:Fin 100:=⟨f.val-1700,by omega⟩
   have h: (⟨1700+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small017 j
 · let j:Fin 100:=⟨f.val-1800,by omega⟩
   have h: (⟨1800+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small018 j
 · let j:Fin 100:=⟨f.val-1900,by omega⟩
   have h: (⟨1900+j.val,by omega⟩:Fin 27280)=f:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact bind_small019 j
end PricingC.NativeFactorGeometry
