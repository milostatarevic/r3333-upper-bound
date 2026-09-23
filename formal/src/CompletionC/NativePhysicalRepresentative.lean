import CompletionC.NativeAfterCoordinates
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativePhysicalRepresentative
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativePairRoleFrame CompletionC.NativeShapeCoordinates CompletionC.NativeSelectedBlocks
open CompletionC.NativeSupportIndex CompletionC.NativeActionVertices CompletionC.NativeAfterCoordinates

theorem selected_vertex_transport {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600)
 (a:Fin (pairTable p).shape.dimension):
 (frame (selectedBlocks b p hf perm i)).vertex
  (supportIndex b (pairTable p).shape hf p hp a)=
 originalVertex b (pairTable p).shape hf p hp perm ((pairTable p).coordinate i a):=by
 have hd:(pairTable p).shape.dimension≤15:=by cases (pairTable p).shape <;> decide
 have ha:a.val<15:=by have h:=a.isLt;omega
 have hb:a.val<PricingC.NativeActionFactors.count (selectedFactor p i):=by
  rw[selected_factor_dimension];exact a.isLt
 have ht:=PricingC.NativeActionPhysical.physical_coordinate_transport (selectedFactor p i)
  (selected_factor_valid p i) (freeFunction b p hf perm)
  (leftMap b (pairTable p).shape p hp i).vertex (rightMap b (pairTable p).shape p hp i).vertex ⟨a.val,ha⟩ hb
 have he:digit (PricingC.NativeActionFactors.coordinateCode (selectedFactor p i)) a.val=
  ((pairTable p).coordinate i a).val:=by
  rw[selected_factor_code]
  exact (selected_coordinate_exact p i a).symm
 exact (after_native b p hf hp perm i a).trans
  (ht.trans ((congrArg (PricingC.NativeActionPhysical.before (selectedFactor p i) (freeFunction b p hf perm)
   (leftMap b (pairTable p).shape p hp i).vertex (rightMap b (pairTable p).shape p hp i).vertex) he).trans
    (before_original b p hf hp perm i ((pairTable p).coordinate i a))))

/-- The exact matrix representative is realized by an injective native frame
whose complete foreign blocks undergo the checked whole-block automorphisms. -/
theorem native_representative {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (hc:NoMonochromaticTriangle c) (p:Fin 737)
 (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape):
 ∃perm:Equiv.Perm (Fin (pairTable p).shape.free),∃i:Fin 600,
 ∀a d:Fin (pairTable p).shape.dimension,a≠d→
 c ((frame (selectedBlocks b p hf perm i)).vertex (supportIndex b (pairTable p).shape hf p hp a))
   ((frame (selectedBlocks b p hf perm i)).vertex (supportIndex b (pairTable p).shape hf p hp d))=
 palette (matrix (pairTable p).shape ((pairTable p).representative ((pairTable p).target i)) a d):=by
 obtain ⟨perm,i,hi⟩:=actual_native_catalogue b hc (pairTable p).shape hf p hp
 refine ⟨perm,i,?_⟩
 intro a d had
 have he:=congrArg₂ (fun x y=>c x y) (selected_vertex_transport b p hf hp perm i a)
  (selected_vertex_transport b p hf hp perm i d)
 exact he.trans ((hi _ _ ((selectedEquiv p i).injective.ne had)).trans
  (congrArg palette (complete_cover (PricingC.NativePairActions.table p) i a d had)).symm)
#print axioms selected_vertex_transport
#print axioms native_representative
end CompletionC.NativePhysicalRepresentative
