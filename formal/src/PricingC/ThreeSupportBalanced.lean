import PricingC.ThreeSupportColors
import PricingABD.Rooted455Catalogue
namespace PricingC.ThreeSupportFrame
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.P15PhysicalRooted (threeIndex palette_threeIndex)

/-- Convert a restored critical-neighborhood equality back to the original
four-color host palette on the same physical vertices. -/
theorem original_palette {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr)
 (hc:NoMonochromaticTriangle c) (a b:Fin (order nf nl nr)) (hab:a≠b) (q:Fin 4)
 (h:(restoredColoring f a b).val=q.val):c (physical f a) (physical f b)=palette q:=by
 have he:(Fin.castLE (by decide) (threeIndex (c (physical f a) (physical f b))):Fin 4)=q:=Fin.ext h
 have hp:=(palette_threeIndex _ (physical_avoids_three f hc a b hab)).symm
 rw[he] at hp
 exact hp

private theorem right_label455 (i:Fin 5):PricingABD.Rooted455Entrance.label2 i=label2 (nf:=4) (nl:=5) (nr:=5) i:=by
 apply Fin.ext;dsimp[PricingABD.Rooted455Entrance.label2,label2];omega
private theorem right_label555 (i:Fin 5):PricingC.Rooted555.label2 i=label2 (nf:=5) (nl:=5) (nr:=5) i:=by
 apply Fin.ext;dsimp[PricingC.Rooted555.label2,label2];omega

/-- Generic actual4|5|5 geometry reaches the exact455native600 catalogue.
No template kinds of the larger foreign blocks enter this argument. -/
theorem actual_455_to_catalogue {c:Host} (f:Frame c 4 5 5) (hc:NoMonochromaticTriangle c):
 ∃p:Equiv.Perm (Fin 4),∃i:Fin 600,∀a b:Fin 14,a≠b →
 c (physical f (PricingABD.Rooted455Free.freeLift p a.castSucc))
   (physical f (PricingABD.Rooted455Free.freeLift p b.castSucc))=
 palette (PricingABD.P15MatrixTransport.matrix (PricingABD.P15MatrixTransport.word (PricingABD.P15PairOrbit.candidate i)) a b):=by
 have hs:∀i,i≠14 → restoredColoring f 14 i=PricingABD.Rooted455Entrance.group i:=restored_root_edges f
 have hl:∀i j:Fin 5,i≠j →
  restoredColoring f (PricingABD.Rooted455Entrance.label1 i) (PricingABD.Rooted455Entrance.label1 j)=PricingABD.Rooted455Data.canonical1 i j:=by
  intro i j hij
  exact (restored_left_edges f i j hij).trans (canonical_left_five i j).1
 have hr:∀i j:Fin 5,i≠j →
  restoredColoring f (PricingABD.Rooted455Entrance.label2 i) (PricingABD.Rooted455Entrance.label2 j)=PricingABD.Rooted455Data.canonical2 i j:=by
  intro i j hij
  rw[right_label455,right_label455]
  exact (restored_right_edges f i j hij).trans (canonical_right_five i j).1
 obtain ⟨p,hp⟩:=PricingABD.Rooted455Free.whole_rooted_normalization (restoredColoring f) (restored_good f hc) hs hl hr
 obtain ⟨i,hi⟩:=PricingABD.Rooted455Catalogue.host_to_exact600
  (PricingABD.Rooted455Free.relabelFree (restoredColoring f) p)
  (PricingABD.Rooted455Free.relabelFree_good _ p (restored_good f hc)) hp
 refine ⟨p,i,?_⟩
 intro a b hab
 apply original_palette f hc _ _ ?_ _ (hi a b hab)
 exact (PricingABD.Rooted455Free.freeLift p).injective.ne
  (by intro h;apply hab;apply Fin.ext;exact congrArg (fun x:Fin 15=>x.val) h)

/-- Generic actual5|5|5 geometry reaches the exact555native600 catalogue.
Only the fivefree vertices are reordered; the original host palette remains. -/
theorem actual_555_to_catalogue {c:Host} (f:Frame c 5 5 5) (hc:NoMonochromaticTriangle c):
 ∃p:Equiv.Perm (Fin 5),∃i:Fin 600,∀a b:Fin 15,a≠b →
 c (physical f (PricingC.Rooted555.freeLift p a.castSucc))
   (physical f (PricingC.Rooted555.freeLift p b.castSucc))=
 palette (PricingC.Rooted555.matrix (PricingC.Rooted555.word (PricingC.Rooted555.candidate i)) a b):=by
 have hs:∀i,i≠15 → restoredColoring f 15 i=PricingC.Rooted555.group i:=restored_root_edges f
 have hl:∀i j:Fin 5,i≠j →
  restoredColoring f (PricingC.Rooted555.label1 i) (PricingC.Rooted555.label1 j)=PricingC.Rooted555.canonical1 i j:=by
  intro i j hij
  exact (restored_left_edges f i j hij).trans (canonical_left_five i j).2
 have hr:∀i j:Fin 5,i≠j →
  restoredColoring f (PricingC.Rooted555.label2 i) (PricingC.Rooted555.label2 j)=PricingC.Rooted555.canonical2 i j:=by
  intro i j hij
  rw[right_label555,right_label555]
  exact (restored_right_edges f i j hij).trans (canonical_right_five i j).2
 obtain ⟨p,i,hi⟩:=PricingC.Rooted555.host_to_exact600_reordering_free
  (restoredColoring f) (restored_good f hc) hs hl hr
 refine ⟨p,i,?_⟩
 intro a b hab
 apply original_palette f hc _ _ ?_ _ (hi a b hab)
 exact (PricingC.Rooted555.freeLift p).injective.ne
  (by intro h;apply hab;apply Fin.ext;exact congrArg (fun x:Fin 16=>x.val) h)

#print axioms actual_455_to_catalogue
#print axioms actual_555_to_catalogue
end PricingC.ThreeSupportFrame
