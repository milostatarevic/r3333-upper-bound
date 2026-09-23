import CompletionC.CommonSupportNormalization
import PricingC.NativeSupportOrders
import PricingG.NativeNegativeSupportTransport
import PricingIntegration.PairNativeBinding
set_option autoImplicit false
namespace CompletionC.NativeRoleGeometry
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingABD.ABGeometry
open PricingIntegration.PhysicalForeignSupport PricingIntegration.PairAdmission
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions
open PricingG.NativeNegativeSupportTransport
open CompletionC.CommonSupportNormalization

def modelKind (large twisted:Bool):Kind:=PricingC.NativePairActions.decodeKind (kindCode large twisted)

noncomputable def ofModel {c:Host} {r:Vertex} {q:Color} (large twisted:Bool)
 (m:PhysicalNeighborhoodMap c r (palette q) (model large twisted)):
 PhysicalNeighborhoodMap c r (palette q) (template (modelKind large twisted)):=by
 cases large <;> cases twisted <;> exact m

theorem ofModel_naturalSupport {c:Host} {r mark:Vertex} (large twisted side:Bool)
 (m:PhysicalNeighborhoodMap c r (palette (owner side)) (model large twisted)):
 naturalSet (support (ofModel large twisted m) mark)=naturalSet (support m mark):=by
 cases large <;> cases twisted <;> rfl

theorem ofModel_palette {c:Host} {r:Vertex} {q:Color} (large twisted:Bool)
 (m:PhysicalNeighborhoodMap c r (palette q) (model large twisted)):
 (ofModel large twisted m).colors=m.colors:=by
 cases large <;> cases twisted <;> rfl

noncomputable def castKind {c:Host} {r:Vertex} {q:Color} {k j:Kind}
 (h:k=j) (m:PhysicalNeighborhoodMap c r (palette q) (template k)):
 PhysicalNeighborhoodMap c r (palette q) (template j):=h ▸ m

theorem castKind_naturalSupport {c:Host} {r mark:Vertex} {side:Bool} {k j:Kind}
 (h:k=j) (m:PhysicalNeighborhoodMap c r (palette (owner side)) (template k)):
 naturalSet (support (castKind h m) mark)=naturalSet (support m mark):=by subst j;rfl

theorem castKind_palette {c:Host} {r:Vertex} {q:Color} {k j:Kind}
 (h:k=j) (m:PhysicalNeighborhoodMap c r (palette q) (template k)):
 (castKind h m).colors=m.colors:=by subst j;rfl

theorem modelKind_order (large twisted:Bool):order (modelKind large twisted)=(if large then 16 else 15):=by
 cases large <;> cases twisted <;> rfl

theorem ofModel_vertex {c:Host} {r:Vertex} {q:Color} (large twisted:Bool)
 (m:PhysicalNeighborhoodMap c r (palette q) (model large twisted))
 (a:Fin (order (modelKind large twisted))) (b:Fin (if large then 16 else 15)) (h:a.val=b.val):
 (ofModel large twisted m).vertex a=m.vertex b:=by
 cases large <;> cases twisted <;> exact congrArg m.vertex (Fin.ext h)

theorem castKind_vertex {c:Host} {r:Vertex} {q:Color} {k j:Kind}
 (h:k=j) (m:PhysicalNeighborhoodMap c r (palette q) (template k))
 (a:Fin (order j)) (b:Fin (order k)) (he:a.val=b.val):
 (castKind h m).vertex a=m.vertex b:=by
 subst j;exact congrArg m.vertex (Fin.ext he)

noncomputable def roleOrder (r:Fin 98):Fin (size r)↪Fin (order (kind r)) where
 toFun i:=orderVertex r i.val
 inj' i j he:=by
  have h5:size r≤5:=by rcases size_four_or_five r with h|h <;> omega
  have hi:i.val<5:=by omega
  have hj:j.val<5:=by omega
  have h:=congrArg Fin.val he
  simp only[orderVertex,Fin.val_mk] at h
  rw[Nat.mod_eq_of_lt (all_role_bounds r ⟨i.val,hi⟩ i.isLt).1,
   Nat.mod_eq_of_lt (all_role_bounds r ⟨j.val,hj⟩ j.isLt).1] at h
  exact Fin.ext (congrArg (fun x:Fin 5=>x.val) (order_injective r ⟨i.val,hi⟩ ⟨j.val,hj⟩ i.isLt j.isLt h))

theorem roleOrder_val (r:Fin 98) (i:Fin (size r)):(roleOrder r i).val=orderLabel r i.val:=by
 have h5:size r≤5:=by rcases size_four_or_five r with h|h <;> omega
 exact Nat.mod_eq_of_lt (all_role_bounds r ⟨i.val,by omega⟩ i.isLt).1

theorem canonicalSupport_natural (r:Fin 98):
 naturalSet (canonicalSupport r)=orderSet orderCodes[r.val]! (size r):=by
 ext v
 simp only[naturalSet,mem_image,mem_canonicalSupport,orderSet,mem_range]
 constructor
 · rintro ⟨u,⟨i,hi,rfl⟩,rfl⟩
   refine ⟨i.val,hi,?_⟩
   exact (roleOrder_val r ⟨i.val,hi⟩).symm
 · rintro ⟨i,hi,rfl⟩
   have h5:size r≤5:=by rcases size_four_or_five r with h|h <;> omega
   exact ⟨orderVertex r i,⟨⟨i,by omega⟩,hi,rfl⟩,roleOrder_val r ⟨i,hi⟩⟩

theorem naturalSet_injective {n:Nat}:Function.Injective (naturalSet (n:=n)):=by
 intro s t h
 exact Finset.image_injective Fin.val_injective h

/-- Exact native order-set binding supplies all positive and negative
support membership facts on the whole critical cell. -/
theorem role_support_exact {c:Host} {r mark:Vertex} {side:Bool} (role:Fin 98)
 (m:PhysicalNeighborhoodMap c r (palette (owner side)) (template (kind role)))
 (h:naturalSet (support m mark)=orderSet orderCodes[role.val]! (size role)):
 support m mark=canonicalSupport role:=
 naturalSet_injective (h.trans (canonicalSupport_natural role).symm)

theorem role_support_edge {c:Host} {r mark:Vertex} {side:Bool} (role:Fin 98)
 (m:PhysicalNeighborhoodMap c r (palette (owner side)) (template (kind role)))
 (h:naturalSet (support m mark)=orderSet orderCodes[role.val]! (size role))
 (i:Fin (size role)):
 c mark (m.vertex (roleOrder role i))=palette 3:=by
 have hm:roleOrder role i∈canonicalSupport role:=by
  have h5:size role≤5:=by rcases size_four_or_five role with h|h <;> omega
  exact (mem_canonicalSupport role _).mpr ⟨⟨i.val,by omega⟩,i.isLt,rfl⟩
 rw[←role_support_exact role m h] at hm
 exact (mem_filter.mp hm).2

/-- The listed native support coordinates carry the required fixed-color
path/cycle on the same physical host. -/
theorem role_pattern {c:Host} {r:Vertex} {side:Bool} (role:Fin 98)
 (m:PhysicalNeighborhoodMap c r (palette (owner side)) (template (kind role)))
 (hp:m.colors=PricingIntegration.BActualFrame.foreignEquiv (owner side))
 (i j:Fin (size role)) (hij:i≠j):
 c (m.vertex (roleOrder role i)) (m.vertex (roleOrder role j))=
 (if PricingC.Rooted45Orientation.Cycle (size role) i.val j.val then palette 0 else palette (if side then 1 else 2)):=by
 have h5:size role≤5:=by rcases size_four_or_five role with h|h <;> omega
 have hi:i.val<5:=by omega
 have hj:j.val<5:=by omega
 have hne:(⟨i.val,hi⟩:Fin 5)≠⟨j.val,hj⟩:=by intro h;apply hij;exact Fin.ext (congrArg (fun x:Fin 5=>x.val) h)
 rw[m.map_color _ _ ((roleOrder role).injective.ne hij),hp]
 change ((PricingIntegration.BActualFrame.foreignEquiv (owner side))
  (template (kind role) (orderVertex role i.val) (orderVertex role j.val))).val=_
 rw[all_canonical_support_orders role ⟨i.val,hi⟩ ⟨j.val,hj⟩ i.isLt j.isLt hne]
 cases side <;> simp only [Bool.false_eq_true,if_false,if_true] <;> split_ifs <;> rfl

#print axioms role_support_exact
#print axioms role_support_edge
end CompletionC.NativeRoleGeometry
