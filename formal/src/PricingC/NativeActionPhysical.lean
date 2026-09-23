import PricingC.NativeFactorGeometryTransport
namespace PricingC.NativeActionPhysical
open PricingC.NativeBlockActions PricingC.NativeBlockAutomorphisms PricingC.NativeActionFactors
attribute [local irreducible]
 PricingC.NativeActionFactors.freeSizesAt PricingC.NativeActionFactors.coordinateCodesAt
 PricingC.NativeActionFactors.freeCodesAt PricingC.NativeActionFactors.leftIdsAt
 PricingC.NativeActionFactors.rightIdsAt
 PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.kinds
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.inducedCodes
set_option maxHeartbeats 0

/-- The free-coordinate factor is an actual permutation of its complete4/5
support, not merely a coordinate function selected by a matrix witness. -/
theorem free_equiv (n code:Nat) (h:FreeValid n code):
 ∃e:Equiv.Perm (Fin n),∀i,(e i).val=digit code i.val:=by
 rcases h with ⟨rfl,h⟩|⟨rfl,h⟩
 · simp only [freeFourCodes,List.mem_cons,List.not_mem_nil,or_false] at h
   let f:Fin 4→Fin 4:=fun i=>⟨digit code i.val%4,Nat.mod_lt _ (by decide)⟩
   have hf:Function.Bijective f:=by rcases h with rfl|rfl <;> decide
   refine ⟨Equiv.ofBijective f hf,?_⟩
   change ∀i:Fin 4, digit code i.val % 4 = digit code i.val
   rcases h with rfl|rfl <;> decide
 · simp only [freeFiveCodes,List.mem_cons,List.not_mem_nil,or_false] at h
   let f:Fin 5→Fin 5:=fun i=>⟨digit code i.val%5,Nat.mod_lt _ (by decide)⟩
   have hf:Function.Bijective f:=by
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
   refine ⟨Equiv.ofBijective f hf,?_⟩
   change ∀i:Fin 5, digit code i.val % 5 = digit code i.val
   rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

noncomputable def before {V:Type} (f:Fin 27280) (free:Nat→V)
 (l:Fin (order (kind (left f)))↪V) (r:Fin (order (kind (right f)))↪V) (i:Nat):V:=
 if i<freeSize f then free i
 else if i<freeSize f+size (left f) then l (orderVertex (left f) (i-freeSize f))
 else r (orderVertex (right f) (i-freeSize f-size (left f)))

noncomputable def after {V:Type} (f:Fin 27280) (free:Nat→V)
 (l:Fin (order (kind (left f)))↪V) (r:Fin (order (kind (right f)))↪V) (i:Nat):V:=
 if i<freeSize f then free (digit (freeCode f) i)
 else if i<freeSize f+size (left f) then
  reindex (kind (left f)) (autoIndex (left f)) l (orderVertex (left f) (i-freeSize f))
 else reindex (kind (right f)) (autoIndex (right f)) r (orderVertex (right f) (i-freeSize f-size (left f)))

/-- Every complete native factor acts by a free-support permutation and two
whole critical-block automorphisms. Its physical vertices agree exactly with
the packed matrix coordinates, so all cross edges retain their original host. -/
theorem physical_coordinate_transport {V:Type} (f:Fin 27280) (hf:Valid f)
 (free:Nat→V) (l:Fin (order (kind (left f)))↪V) (r:Fin (order (kind (right f)))↪V)
 (i:Fin 15) (hi:i.val<count f):
 after f free l r i.val=before f free l r (digit (coordinateCode f) i.val):=by
 obtain ⟨hfree,hcount,hcoord⟩:=hf
 rw[hcoord i hi]
 by_cases h0:i.val<freeSize f
 · have hb:digit (freeCode f) i.val<freeSize f:=by
    obtain ⟨e,he⟩:=free_equiv _ _ hfree
    rw[←he ⟨i.val,h0⟩]
    exact (e ⟨i.val,h0⟩).isLt
   simp only[after,before,combinedCoordinate,if_pos h0,if_pos hb]
 · by_cases h1:i.val<freeSize f+size (left f)
   · have hj:i.val-freeSize f<size (left f):=by omega
     have hj5:i.val-freeSize f<5:=by
      rcases size_four_or_five (left f) with h|h <;> omega
     have hb:inducedLabel (left f) (i.val-freeSize f)<size (left f):=
      (all_role_bounds (left f) ⟨_,hj5⟩ hj).2
     have hn:¬freeSize f+inducedLabel (left f) (i.val-freeSize f)<freeSize f:=by omega
     have hy:freeSize f+inducedLabel (left f) (i.val-freeSize f)<freeSize f+size (left f):=by omega
     simp only[after,before,combinedCoordinate,if_neg h0,if_pos h1,if_neg hn,if_pos hy]
     rw[physical_role_extension (left f) l ⟨_,hj5⟩ hj]
     congr 2
     simp only [Fin.val_mk]
     omega
   · have hj:i.val-freeSize f-size (left f)<size (right f):=by unfold count at hi;omega
     have hj5:i.val-freeSize f-size (left f)<5:=by
      rcases size_four_or_five (right f) with h|h <;> omega
     have hb:inducedLabel (right f) (i.val-freeSize f-size (left f))<size (right f):=
      (all_role_bounds (right f) ⟨_,hj5⟩ hj).2
     have hn:¬freeSize f+size (left f)+inducedLabel (right f) (i.val-freeSize f-size (left f))<freeSize f:=by omega
     have hy:¬freeSize f+size (left f)+inducedLabel (right f) (i.val-freeSize f-size (left f))<freeSize f+size (left f):=by omega
     simp only[after,before,combinedCoordinate,if_neg h0,if_neg h1,if_neg hn,if_neg hy]
     rw[physical_role_extension (right f) r ⟨_,hj5⟩ hj]
     congr 2
     simp only [Fin.val_mk]
     omega

theorem physical_edge_transport {V C:Type} (f:Fin 27280) (hf:Valid f)
 (free:Nat→V) (l:Fin (order (kind (left f)))↪V) (r:Fin (order (kind (right f)))↪V)
 (host:V→V→C) (a b:Fin 15) (ha:a.val<count f) (hb:b.val<count f):
 host (after f free l r a.val) (after f free l r b.val)=
 host (before f free l r (digit (coordinateCode f) a.val))
      (before f free l r (digit (coordinateCode f) b.val)):=by
 rw[physical_coordinate_transport f hf free l r a ha,
    physical_coordinate_transport f hf free l r b hb]
#print axioms free_equiv
#print axioms physical_edge_transport
end PricingC.NativeActionPhysical
