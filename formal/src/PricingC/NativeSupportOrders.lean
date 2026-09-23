import PricingC.NativeBlockActions
import PricingC.Rooted45Orientation
namespace PricingC.NativeBlockActions
open PricingC.NativeBlockAutomorphisms
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Every original native physical_order is the required coloredP4/C5 order.
Both foreign block palettes map local0 toglobal0 and local1 to the other
allowed internalcolor; local2 is the omitted attachingcolor. -/
theorem all_canonical_support_orders : ∀r:Fin 98,∀i j:Fin 5,
 i.val<size r → j.val<size r → i≠j →
 template (kind r) (orderVertex r i.val) (orderVertex r j.val)=
 (if PricingC.Rooted45Orientation.Cycle (size r) i.val j.val then 0 else 1):=by decide +kernel

#print axioms all_canonical_support_orders
end PricingC.NativeBlockActions
