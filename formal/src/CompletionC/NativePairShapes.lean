import CompletionC.NativePairShape0
import CompletionC.NativePairShape1
import CompletionC.NativePairShape2
import CompletionC.NativePairShape3
import CompletionC.NativePairShape4
import CompletionC.NativePairShape5
import CompletionC.NativePairShape6
import CompletionC.NativePairShape7
namespace CompletionC.NativeMatrices
open PricingC
attribute [local irreducible] PairShape
set_option maxHeartbeats 0
theorem pair_shape (p:Fin 737):PairShape p:=by
 have h:p.val/100<8:=by omega
 interval_cases hq:p.val/100
 · let j:Fin 100:=⟨p.val-0,by omega⟩
   have he:(⟨0+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_0 j
 · let j:Fin 100:=⟨p.val-100,by omega⟩
   have he:(⟨100+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_1 j
 · let j:Fin 100:=⟨p.val-200,by omega⟩
   have he:(⟨200+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_2 j
 · let j:Fin 100:=⟨p.val-300,by omega⟩
   have he:(⟨300+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_3 j
 · let j:Fin 100:=⟨p.val-400,by omega⟩
   have he:(⟨400+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_4 j
 · let j:Fin 100:=⟨p.val-500,by omega⟩
   have he:(⟨500+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_5 j
 · let j:Fin 100:=⟨p.val-600,by omega⟩
   have he:(⟨600+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_6 j
 · let j:Fin 37:=⟨p.val-700,by omega⟩
   have he:(⟨700+j.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[j];omega
   rw[←he];exact pair_shape_7 j

theorem pair_dimensions (p:Fin 737):
 NativePairActions.freeSizes[p.val]! = (table (NativePairActions.table p)).shape.free ∧
 NativePairActions.leftSizes[p.val]! = (table (NativePairActions.table p)).shape.left ∧
 NativePairActions.rightSizes[p.val]! = (table (NativePairActions.table p)).shape.right:=by
 obtain ⟨_,_,hf,hl,hr,_,_⟩:=PricingIntegration.PairAdmission.all_native_bindings p
 have hs:=pair_shape p
 unfold PairShape at hs
 rw[←hs] at hf hl hr
 have hf' (s:Shape): (if s.code=0 then 4 else 5)=s.free:=by cases s <;> rfl
 have hl' (s:Shape): (if s.code=1 then 4 else 5)=s.left:=by cases s <;> rfl
 have hr' (s:Shape): (if s.code=2 then 4 else 5)=s.right:=by cases s <;> rfl
 exact ⟨hf.trans (hf' _),hl.trans (hl' _),hr.trans (hr' _)⟩
#print axioms pair_shape
#print axioms pair_dimensions
end CompletionC.NativeMatrices
