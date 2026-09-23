import PricingC.Rooted45Catalogue
import PricingC.Rooted45Physical

namespace PricingC.Rooted45Orientation
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.P15PhysicalRooted (threeIndex palette_threeIndex)

/-- Both545 and554 actual physical support configurations lie in their exact
retained600word catalogue. The result uses the original four-color palette;
only the same free-five vertices are reordered. -/
theorem physical_host_to_exact600 {k : Bool} {c : Host} (f : Physical45 k c)
 (hc : NoMonochromaticTriangle c) :
 ∃p:Equiv.Perm (Fin 5),∃i:Fin 600,∀a b:Fin 14,a≠b →
 c (f.physical (OwnFive15.freeLift p a.castSucc))
   (f.physical (OwnFive15.freeLift p b.castSucc))=
 palette (matrix k (word (candidate k i)) a b) := by
 obtain ⟨p,i,hi⟩:=host_to_exact600_reordering_free k (restoredColoring f)
  (restored_good f hc) (restored_foreign f)
 refine ⟨p,i,?_⟩
 intro a b hab
 have hh:=hi a b hab
 change (threeIndex (c (f.physical (OwnFive15.freeLift p a.castSucc))
  (f.physical (OwnFive15.freeLift p b.castSucc)))).val=_ at hh
 have he:(Fin.castLE (by decide) (threeIndex (c (f.physical (OwnFive15.freeLift p a.castSucc))
  (f.physical (OwnFive15.freeLift p b.castSucc)))) : Fin 4)=
  matrix k (word (candidate k i)) a b:=Fin.ext hh
 have hne:OwnFive15.freeLift p a.castSucc≠OwnFive15.freeLift p b.castSucc:=
  (OwnFive15.freeLift p).injective.ne (by intro h;apply hab;apply Fin.ext;exact congrArg (fun x:Fin 15=>x.val) h)
 have hp:=(palette_threeIndex _ (physical_avoids_three f hc _ _ hne)).symm
 rw [he] at hp
 exact hp

#print axioms physical_host_to_exact600
#check physical_host_to_exact600
end PricingC.Rooted45Orientation
