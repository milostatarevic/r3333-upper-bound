import CompletionC.NativeSuffix
import CompletionC.NativeSignedSupport
import CompletionC.NativeFreeGeometry
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativeSuffixSat
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingABD PricingABD.ABLayout PricingIntegration.PairAdmission
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativeSupportIndex CompletionC.NativeSuffix

def EdgeTruth {c:Host} {l:Layout} (w:Valuation) (f:Frame c l):Prop:=
 ∀u v:Fin (vertexCount l),∀q:Fin 4,u≠v→
 (w (PricingIntegration.NativePrimaryCore.edgeVar u v q)=true ↔c (f.vertex u) (f.vertex v)=palette q)

theorem mark_ne_left (l:Layout) (v:Fin (leftSize l)):mark l≠left l v:=by
 intro h
 have he:=congrArg (owner l) h
 change owner l (marked l 15)=owner l (left l v) at he
 rw[owner_marked,owner_left] at he
 contradiction

theorem mark_ne_right (l:Layout) (v:Fin (rightSize l)):mark l≠right l v:=by
 intro h
 have he:=congrArg (owner l) h
 change owner l (marked l 15)=owner l (right l v) at he
 rw[owner_marked,owner_right] at he
 contradiction

theorem matrixUnits_true {c:Host} {l:Layout} {t:Types} (b z:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape) (j:Fin (pairTable p).count)
 (w:Valuation) (hw:EdgeTruth w (frame z))
 (hmat:∀a d:Fin (pairTable p).shape.dimension,a≠d→
 c ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp a))
   ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp d))=
 palette (matrix (pairTable p).shape ((pairTable p).representative j) a d)):
 ∀lit∈matrixUnits l p j,w lit.2=lit.1:=by
 intro lit h
 obtain ⟨ab,hab,rfl⟩:=List.mem_map.mp h
 have hne:=pair_ne l p ab hab
 have hn:=(supportIndex_injective b (pairTable p).shape hf p hp).ne hne
 change w (edgeNat _ _ _ _)=true
 have he:edgeNat (vertexCount l) (label l p ab.1.val) (label l p ab.2.val)
  (matrix (pairTable p).shape ((pairTable p).representative j) ab.1 ab.2)=
  PricingIntegration.NativePrimaryCore.edgeVar
   (supportIndex b (pairTable p).shape hf p hp ab.1)
   (supportIndex b (pairTable p).shape hf p hp ab.2)
   (matrix (pairTable p).shape ((pairTable p).representative j) ab.1 ab.2):=by
  rw[label_supportIndex b p hf hp ab.1,label_supportIndex b p hf hp ab.2,edgeNat_fin]
 rw[he]
 exact (hw _ _ _ hn).mpr (hmat ab.1 ab.2 hne)

theorem signedUnits_true {c:Host} {l:Layout} {t:Types} (z:Blocks c l t)
 (p:Fin 737) (w:Valuation) (hw:EdgeTruth w (frame z))
 (hl:∀v:Fin (leftSize l),c (z.marked.vertex 15) (z.left.vertex v)=palette 3 ↔v.val∈(retained p).left)
 (hr:∀v:Fin (rightSize l),c (z.marked.vertex 15) (z.right.vertex v)=palette 3 ↔v.val∈(retained p).right):
 ∀lit∈signedUnits l p,w lit.2=lit.1:=by
 intro lit h
 rcases List.mem_append.mp h with h|h
 · obtain ⟨v,_,rfl⟩:=List.mem_map.mp h
   change w (edgeNat _ _ _ _)=decide _
   rw[edgeNat_fin]
   apply Bool.eq_iff_iff.mpr
   simp only[decide_eq_true_eq]
   have he:=hw (mark l) (left l v) 3 (mark_ne_left l v)
   change _ ↔c (physical z (marked l 15)) (physical z (left l v))=palette 3 at he
   rw[physical_marked,physical_left] at he
   exact he.trans (hl v)
 · obtain ⟨v,_,rfl⟩:=List.mem_map.mp h
   change w (edgeNat _ _ _ _)=decide _
   rw[edgeNat_fin]
   apply Bool.eq_iff_iff.mpr
   simp only[decide_eq_true_eq]
   have he:=hw (mark l) (right l v) 3 (mark_ne_right l v)
   change _ ↔c (physical z (marked l 15)) (physical z (right l v))=palette 3 at he
   rw[physical_marked,physical_right] at he
   exact he.trans (hr v)

/-- Physical edge truth supplies every original positive and negative unit.
The prefix may use arbitrary auxiliary atoms outside these preserved edges. -/
theorem suffix_sat {c:Host} {l:Layout} {t:Types} (b z:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape) (j:Fin (pairTable p).count)
 (w:Valuation) (hw:EdgeTruth w (frame z))
 (hl:∀v:Fin (leftSize l),c (z.marked.vertex 15) (z.left.vertex v)=palette 3 ↔v.val∈(retained p).left)
 (hr:∀v:Fin (rightSize l),c (z.marked.vertex 15) (z.right.vertex v)=palette 3 ↔v.val∈(retained p).right)
 (hmat:∀a d:Fin (pairTable p).shape.dimension,a≠d→
 c ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp a))
   ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp d))=
 palette (matrix (pairTable p).shape ((pairTable p).representative j) a d)):
 FormulaSat w (formula l p j):=by
 intro clause hc
 obtain ⟨lit,hlit,rfl⟩:=List.mem_map.mp hc
 refine ⟨lit,by simp,?_⟩
 rcases List.mem_append.mp hlit with hs|hm
 · split_ifs at hs
   · simp at hs
   · exact signedUnits_true z p w hw hl hr lit hs
 · exact matrixUnits_true b z p hf hp j w hw hmat lit hm
#print axioms suffix_sat
end CompletionC.NativeSuffixSat
