import PricingC.Rooted45Lookup
import PricingC.Rooted45Free

namespace PricingC.Rooted45Orientation
open R4333

/-- All relabeling and palette recoding used to invoke455 are undone here:
the returned matrix describes the original fixed colors and block coordinates. -/
theorem canonical_host_to_exact600 (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor)
 (hc:NoMonochromaticTriangle c) (h:Canonical k c) :
 ∃i:Fin 600,∀a b:Fin 14,a≠b →
 (c a.castSucc b.castSucc).val=(matrix k (word (candidate k i)) a b).val := by
 obtain ⟨i,hi⟩:=PricingABD.Rooted455Catalogue.host_to_exact600
  (transport k c) (transport_good k c hc) (transport_canonical k c h)
 refine ⟨target k i,?_⟩
 intro a b hab
 have hh:=hi (oldIndex k a) (oldIndex k b) ((oldIndex_injective k).ne hab)
 change (colors k (c (vertices k (oldIndex k a).castSucc) (vertices k (oldIndex k b).castSucc))).val=_ at hh
 rw [oldIndex_cast,oldIndex_cast,Equiv.apply_symm_apply,Equiv.apply_symm_apply] at hh
 have hh4:(colors k (c a.castSucc b.castSucc)).castSucc=
  PricingABD.P15MatrixTransport.matrix
   (PricingABD.P15MatrixTransport.word (PricingABD.P15PairOrbit.candidate i))
   (oldIndex k a) (oldIndex k b):=Fin.ext hh
 rw [full_matrix_transport k i a b hab,←hh4,colorBack_cast,Equiv.symm_apply_apply]

theorem host_to_exact600_reordering_free (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor)
 (hc:NoMonochromaticTriangle c) (h:ForeignCanonical k c) :
 ∃p:Equiv.Perm (Fin 5),∃i:Fin 600,∀a b:Fin 14,a≠b →
 (c (OwnFive15.freeLift p a.castSucc) (OwnFive15.freeLift p b.castSucc)).val=
 (matrix k (word (candidate k i)) a b).val := by
 obtain ⟨p,hp⟩:=free_normalization k c hc h
 obtain ⟨i,hi⟩:=canonical_host_to_exact600 k (OwnFive15.relabelFree c p)
  (OwnFive15.relabelFree_good c p hc) hp
 exact ⟨p,i,hi⟩

#print axioms canonical_host_to_exact600
#print axioms host_to_exact600_reordering_free
end PricingC.Rooted45Orientation
