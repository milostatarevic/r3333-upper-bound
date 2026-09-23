import PricingC.GScopeAgreement

namespace PricingC.GIsomorphic
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout
open PricingC.GRelations

def fastBaseCore (x : Fin 2) (y : Fin 72) (g : Fin 25) : CoreBase := fun a b =>
  if a = b then none
  else if a = 0 then some (if b.val ≤ 16 then 0 else 1)
  else if b = 0 then some (if a.val ≤ 16 then 0 else 1)
  else if a.val ≤ 16 then
    if b.val ≤ 16 then some (xPalette (fastColor (rootRow x) (blockPoint a) (blockPoint b)))
    else crossColor g (blockPoint a) (blockPoint b)
  else if b.val ≤ 16 then crossColor g (blockPoint b) (blockPoint a)
  else some (yPalette (fastColor (censusRow y) (blockPoint a) (blockPoint b)))

theorem fastBaseCore_exact (x : Fin 2) (y : Fin 72) (g : Fin 25) :
 fastBaseCore x y g=baseCore x y g := by
 funext a b
 simp only [fastBaseCore,baseCore,rootColor,nativeColor,fastColor_exact]

#print axioms fastBaseCore_exact
end PricingC.GIsomorphic
