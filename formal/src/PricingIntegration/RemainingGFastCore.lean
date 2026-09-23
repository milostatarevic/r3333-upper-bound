import PricingIntegration.RemainingGRefinement
import PricingC.GRelations

namespace PricingIntegration.RemainingGCore
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingC.GLayoutRefinement
open PricingC PricingC.GIsomorphic PricingG.Completion72 PricingC.GRelations

def fastCross (d : Fin 72) (x y : Fin 16) : Option Color :=
  if xorGraph.Adj x y then some 1
  else if fastColor (censusRow d) x y = 1 then some 0
  else none

def fastBase (kind : Fin 2) (d y : Fin 72) (u v : Fin 33) : Option Color :=
  if u = v then none else
  match view u,view v with
  | none,none => none
  | none,some (side,_) => some (if side then 1 else 0)
  | some (side,_),none => some (if side then 1 else 0)
  | some (false,a),some (false,b) => some (xColors (fastColor (rootRow kind) a b))
  | some (true,a),some (true,b) => some (yColors (fastColor (censusRow y) ((decompEquiv d).symm a) ((decompEquiv d).symm b)))
  | some (false,a),some (true,b) => fastCross d a b
  | some (true,a),some (false,b) => fastCross d b a

theorem fastBase_exact (kind : Fin 2) (d y : Fin 72) : fastBase kind d y = base kind d y := by
  funext u v
  simp only [fastBase,base,fastCross,cross,fastColor_exact,nativeColor,rootColor]
  rfl

#print axioms fastBase_exact
end PricingIntegration.RemainingGCore
