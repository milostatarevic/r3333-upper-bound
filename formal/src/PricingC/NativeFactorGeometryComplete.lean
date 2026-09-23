import PricingC.NativeFactorGeometrySmall00
import PricingC.NativeFactorGeometrySmall01
import PricingC.NativeFactorGeometrySmall02
import PricingC.NativeFactorGeometrySmall03
import PricingC.NativeFactorGeometrySmall04
import PricingC.NativeFactorGeometrySmall05
import PricingC.NativeFactorGeometrySmall06
import PricingC.NativeFactorGeometrySmall07
import PricingC.NativeFactorGeometrySmall08
import PricingC.NativeFactorGeometrySmall09
import PricingC.NativeFactorGeometrySmall10
import PricingC.NativeFactorGeometrySmall11
import PricingC.NativeFactorGeometrySmall12
import PricingC.NativeFactorGeometrySmall13
namespace PricingC.NativeFactorGeometry
attribute [local irreducible] Good geometryOf
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_geometry_good (g:Fin 1390):Good g:=by
 have hq:g.val/100<14:=by omega
 interval_cases heq:g.val/100
 · let j:Fin 100:=⟨g.val-0,by omega⟩
   have h: (⟨0+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small00 j
 · let j:Fin 100:=⟨g.val-100,by omega⟩
   have h: (⟨100+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small01 j
 · let j:Fin 100:=⟨g.val-200,by omega⟩
   have h: (⟨200+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small02 j
 · let j:Fin 100:=⟨g.val-300,by omega⟩
   have h: (⟨300+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small03 j
 · let j:Fin 100:=⟨g.val-400,by omega⟩
   have h: (⟨400+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small04 j
 · let j:Fin 100:=⟨g.val-500,by omega⟩
   have h: (⟨500+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small05 j
 · let j:Fin 100:=⟨g.val-600,by omega⟩
   have h: (⟨600+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small06 j
 · let j:Fin 100:=⟨g.val-700,by omega⟩
   have h: (⟨700+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small07 j
 · let j:Fin 100:=⟨g.val-800,by omega⟩
   have h: (⟨800+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small08 j
 · let j:Fin 100:=⟨g.val-900,by omega⟩
   have h: (⟨900+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small09 j
 · let j:Fin 100:=⟨g.val-1000,by omega⟩
   have h: (⟨1000+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small10 j
 · let j:Fin 100:=⟨g.val-1100,by omega⟩
   have h: (⟨1100+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small11 j
 · let j:Fin 100:=⟨g.val-1200,by omega⟩
   have h: (⟨1200+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small12 j
 · let j:Fin 90:=⟨g.val-1300,by omega⟩
   have h: (⟨1300+j.val,by omega⟩:Fin 1390)=g:=by apply Fin.ext;dsimp[j];omega
   rw[←h]
   exact geometry_small13 j

#print axioms all_geometry_good
end PricingC.NativeFactorGeometry
