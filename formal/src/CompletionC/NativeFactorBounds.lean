import PricingC.NativeActionPhysical
import PricingC.NativePairsComplete
set_option autoImplicit false
namespace CompletionC.NativeFactorBounds
open PricingC.NativeBlockActions PricingC.NativeActionFactors
attribute [local irreducible]
 PricingC.NativeActionFactors.freeSizesAt PricingC.NativeActionFactors.coordinateCodesAt
 PricingC.NativeActionFactors.freeCodesAt PricingC.NativeActionFactors.leftIdsAt
 PricingC.NativeActionFactors.rightIdsAt PricingC.NativeBlockActions.sizes
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.inducedCodes

private theorem free_bound (n code a:Nat) (h:FreeValid n code) (ha:a<n):digit code a<n:=by
 obtain ⟨e,he⟩:=PricingC.NativeActionPhysical.free_equiv n code h
 rw[←he ⟨a,ha⟩]
 exact (e ⟨a,ha⟩).isLt
private theorem free_inj (n code a b:Nat) (h:FreeValid n code) (ha:a<n) (hb:b<n)
 (he:digit code a=digit code b):a=b:=by
 obtain ⟨e,hv⟩:=PricingC.NativeActionPhysical.free_equiv n code h
 have heq:e ⟨a,ha⟩=e ⟨b,hb⟩:=by apply Fin.ext;simpa only[hv] using he
 exact congrArg Fin.val (e.injective heq)
private theorem induced_bound (r:Fin 98) (a:Nat) (ha:a<size r):inducedLabel r a<size r:=by
 have ha5:a<5:=by rcases size_four_or_five r with h|h <;> omega
 exact (all_role_bounds r ⟨a,ha5⟩ ha).2
private theorem induced_inj (r:Fin 98) (a b:Nat) (ha:a<size r) (hb:b<size r)
 (he:inducedLabel r a=inducedLabel r b):a=b:=by
 have ha5:a<5:=by rcases size_four_or_five r with h|h <;> omega
 have hb5:b<5:=by rcases size_four_or_five r with h|h <;> omega
 exact congrArg Fin.val (induced_injective r ⟨a,ha5⟩ ⟨b,hb5⟩ ha hb he)

private theorem free_apply (f:Fin 27280) (a:Nat) (ha:a<freeSize f):
 combinedCoordinate f a=digit (freeCode f) a:=by simp only[combinedCoordinate,if_pos ha]
private theorem left_apply (f:Fin 27280) (a:Nat) (h0:¬a<freeSize f)
 (h1:a<freeSize f+size (left f)):
 combinedCoordinate f a=freeSize f+inducedLabel (left f) (a-freeSize f):=by
 simp only[combinedCoordinate,if_neg h0,if_pos h1]
private theorem right_apply (f:Fin 27280) (a:Nat) (h0:¬a<freeSize f)
 (h1:¬a<freeSize f+size (left f)):
 combinedCoordinate f a=freeSize f+size (left f)+inducedLabel (right f) (a-freeSize f-size (left f)):=by
 simp only[combinedCoordinate,if_neg h0,if_neg h1]

theorem combined_bound (f:Fin 27280) (hf:Valid f) (a:Nat) (ha:a<count f):
 combinedCoordinate f a<count f:=by
 by_cases h0:a<freeSize f
 · rw[free_apply f a h0]
   have h:=free_bound _ _ a hf.1 h0
   unfold count;omega
 · by_cases h1:a<freeSize f+size (left f)
   · rw[left_apply f a h0 h1]
     have h:=induced_bound (left f) (a-freeSize f) (by omega)
     unfold count;omega
   · rw[right_apply f a h0 h1]
     have hj:a-freeSize f-size (left f)<size (right f):=by unfold count at ha;omega
     have h:=induced_bound (right f) _ hj
     unfold count;omega

theorem combined_injective (f:Fin 27280) (hf:Valid f) (a b:Nat)
 (ha:a<count f) (hb:b<count f) (he:combinedCoordinate f a=combinedCoordinate f b):a=b:=by
 by_cases ha0:a<freeSize f
 · rw[free_apply f a ha0] at he
   have hfa:=free_bound _ _ a hf.1 ha0
   by_cases hb0:b<freeSize f
   · rw[free_apply f b hb0] at he
     exact free_inj _ _ a b hf.1 ha0 hb0 he
   · by_cases hb1:b<freeSize f+size (left f)
     · rw[left_apply f b hb0 hb1] at he;omega
     · rw[right_apply f b hb0 hb1] at he;omega
 · by_cases ha1:a<freeSize f+size (left f)
   · rw[left_apply f a ha0 ha1] at he
     have hal:a-freeSize f<size (left f):=by omega
     have hla:=induced_bound (left f) _ hal
     by_cases hb0:b<freeSize f
     · rw[free_apply f b hb0] at he
       have hfb:=free_bound _ _ b hf.1 hb0
       omega
     · by_cases hb1:b<freeSize f+size (left f)
       · rw[left_apply f b hb0 hb1] at he
         have hbl:b-freeSize f<size (left f):=by omega
         have hsub:=induced_inj (left f) (a-freeSize f) (b-freeSize f) hal hbl (by omega)
         omega
       · rw[right_apply f b hb0 hb1] at he;omega
   · rw[right_apply f a ha0 ha1] at he
     have har:a-freeSize f-size (left f)<size (right f):=by unfold count at ha;omega
     by_cases hb0:b<freeSize f
     · rw[free_apply f b hb0] at he
       have hfb:=free_bound _ _ b hf.1 hb0
       omega
     · by_cases hb1:b<freeSize f+size (left f)
       · rw[left_apply f b hb0 hb1] at he
         have hbl:b-freeSize f<size (left f):=by omega
         have hlb:=induced_bound (left f) _ hbl
         omega
       · rw[right_apply f b hb0 hb1] at he
         have hbr:b-freeSize f-size (left f)<size (right f):=by unfold count at hb;omega
         have hsub:=induced_inj (right f) (a-freeSize f-size (left f))
          (b-freeSize f-size (left f)) har hbr (by omega)
         omega

theorem coordinate_bound (f:Fin 27280) (hf:Valid f) (a:Nat) (ha:a<count f):
 digit (coordinateCode f) a<count f:=by
 have ha15:a<15:=by rcases hf.2.1 with h|h <;> omega
 rw[hf.2.2 ⟨a,ha15⟩ ha]
 exact combined_bound f hf a ha

theorem coordinate_injective (f:Fin 27280) (hf:Valid f) (a b:Nat)
 (ha:a<count f) (hb:b<count f) (he:digit (coordinateCode f) a=digit (coordinateCode f) b):a=b:=by
 have ha15:a<15:=by rcases hf.2.1 with h|h <;> omega
 have hb15:b<15:=by rcases hf.2.1 with h|h <;> omega
 rw[hf.2.2 ⟨a,ha15⟩ ha,hf.2.2 ⟨b,hb15⟩ hb] at he
 exact combined_injective f hf a b ha hb he
#print axioms coordinate_bound
#print axioms coordinate_injective
end CompletionC.NativeFactorBounds
