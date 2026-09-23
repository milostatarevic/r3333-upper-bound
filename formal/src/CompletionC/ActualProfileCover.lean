import CompletionC.CommonEntrance
import CompletionC.NativeFamilyJoin
set_option autoImplicit false
namespace CompletionC.ActualProfileCover
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter Ramsey61.CPhysicalNormalization
open PricingABD.ABLayout CompletionC.CommonBlocks CompletionC.NativeMatrices CompletionC.NativeFamilyJoin

def NativeExclusions:Prop:=∀l t p,Admitted l t p→∀j:Fin (pairTable p).count,∀w:Valuation,¬FormulaSat w (formula l t p j)

theorem actual_A_cover (c:Host) (hc:NoMonochromaticTriangle c) (r:Vertex)
 (hw:W c r=48) (hh:48≤H c r):
 ∃five:Bool,∃t:Types,∃p:Fin 737,Admitted ⟨.A,five⟩ t p ∧
 ∃j:Fin (pairTable p).count,∃w:Valuation,FormulaSat w (formula ⟨.A,five⟩ t p j):=by
 obtain ⟨σ,good,_,_,five,t,b,_,h01,h12⟩:=CompletionC.CommonEntrance.actual_A c hc r hw hh
 obtain ⟨p,hp,j,w,hs⟩:=common_native_cover b good ⟨h01,h12⟩
 exact ⟨five,t,p,hp,j,w,hs⟩

theorem actual_B_cover (c:Host) (hc:NoMonochromaticTriangle c) (r:Vertex)
 (hw:W c r=47) (hh:47≤H c r):
 ∃five:Bool,∃t:Types,∃p:Fin 737,Admitted ⟨.B,five⟩ t p ∧
 ∃j:Fin (pairTable p).count,∃w:Valuation,FormulaSat w (formula ⟨.B,five⟩ t p j):=by
 obtain ⟨σ,good,_,_,five,t,b,_,ht⟩:=CompletionC.CommonEntrance.actual_B c hc r hw hh
 obtain ⟨p,hp,j,w,hs⟩:=common_native_cover b good ht
 exact ⟨five,t,p,hp,j,w,hs⟩

/-- D's two U/U owners remain genuinely separate. The other four owners
reach the exact common native family without another mathematical premise. -/
theorem actual_D_cover_or_UU (c:Host) (hc:NoMonochromaticTriangle c) (r:Vertex)
 (hw:W c r=46) (hh:46≤H c r):
 ∃σ:FourColor≃FourColor,let d:=relabel c (Equiv.refl _) σ
 NoMonochromaticTriangle d ∧∃five:Bool,∃t:Types,∃b:Blocks d ⟨.D,five⟩ t,b.root=r ∧
 ((t.left=false∧t.right=false)∨
  ∃p:Fin 737,Admitted ⟨.D,five⟩ t p∧∃j:Fin (pairTable p).count,∃w:Valuation,
   FormulaSat w (formula ⟨.D,five⟩ t p j)):=by
 obtain ⟨σ,good,_,five,t,b,hr,ho⟩:=CompletionC.CommonEntrance.actual_D c hc r hw hh
 refine ⟨σ,good,five,t,b,hr,?_⟩
 cases ht:t.right with
 | false=>left;exact ⟨ho.resolve_right (by simp[ht]),rfl⟩
 | true=>right;exact common_native_cover b good ht

theorem actual_A_excluded (native:NativeExclusions) (c:Host) (hc:NoMonochromaticTriangle c)
 (r:Vertex) (hw:W c r=48) (hh:48≤H c r):False:=by
 obtain ⟨five,t,p,hp,j,w,hs⟩:=actual_A_cover c hc r hw hh
 exact native _ _ _ hp j w hs

theorem actual_B_excluded (native:NativeExclusions) (c:Host) (hc:NoMonochromaticTriangle c)
 (r:Vertex) (hw:W c r=47) (hh:47≤H c r):False:=by
 obtain ⟨five,t,p,hp,j,w,hs⟩:=actual_B_cover c hc r hw hh
 exact native _ _ _ hp j w hs
#print axioms actual_A_cover
#print axioms actual_B_cover
#print axioms actual_D_cover_or_UU
#print axioms actual_A_excluded
end CompletionC.ActualProfileCover
