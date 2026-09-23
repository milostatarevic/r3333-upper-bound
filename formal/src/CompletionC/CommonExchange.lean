import CompletionC.CommonPairAdmission
import PricingG.DPhysicalExchange
set_option autoImplicit false
namespace CompletionC.CommonExchange
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open Ramsey61.CPhysicalNormalization PricingABD PricingABD.ABLayout PricingABD.TTExchange
open PricingIntegration.BActualFrame PricingIntegration.PhysicalForeignSupport
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices

def swapTypes (t:Types):Types:=⟨t.right,t.left,t.marked⟩
noncomputable def toD {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t):
 PricingG.DPhysicalBlocks.Blocks c b.root (freeSize ⟨.D,five⟩):=
 ⟨b.free,t.left,t.right,t.marked,b.left,b.right,b.marked,b.free_mem,b.left_palette,b.right_palette,
 b.marked_palette,b.marked_high,b.free_own,b.free_exact⟩

noncomputable def exchange {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t):
 Blocks (swappedHost c) ⟨.D,five⟩ (swapTypes t):=by
 let z:=(toD b).exchange
 refine ⟨b.root,z.free,z.m,z.x,z.q,z.free_mem,z.m_palette,z.x_palette,z.q_palette,?_,?_,z.marked_high,z.free_own,z.free_exact⟩
 · change colorDegree (relabel c (Equiv.refl _) colorSwap) (palette 0) b.root=_
   rw[relabel_degree]
   exact b.low_degree
 · rw[swappedHost_H]
   exact b.selected

@[simp] theorem exchange_root {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t):
 (exchange b).root=b.root:=rfl
@[simp] theorem exchange_mark {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t):
 (exchange b).marked.vertex 15=b.marked.vertex 15:=(toD b).exchangeQ_mark
@[simp] theorem exchange_left {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t) (i:Fin 15):
 (exchange b).left.vertex i=b.right.vertex i:=rfl
@[simp] theorem exchange_right {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t) (i:Fin 15):
 (exchange b).right.vertex i=b.left.vertex i:=rfl

theorem exchange_left_support {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t):
 support (side:=false) (exchange b).left ((exchange b).marked.vertex 15)=
 support (side:=true) b.right (b.marked.vertex 15):=by
 ext i
 simp only[support,Finset.mem_filter,Finset.mem_univ,true_and,exchange_mark,exchange_left,swappedHost_apply]
 change colorSwap.symm (c (b.marked.vertex 15) (b.right.vertex i))=colorSwap.symm (palette 3) ↔ _
 constructor
 · intro h;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,colorSwap.symm.injective h⟩
 · intro h;exact congrArg colorSwap.symm (Finset.mem_filter.mp h).2

theorem exchange_right_support {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t):
 support (side:=true) (exchange b).right ((exchange b).marked.vertex 15)=
 support (side:=false) b.left (b.marked.vertex 15):=by
 ext i
 simp only[support,Finset.mem_filter,Finset.mem_univ,true_and,exchange_mark,exchange_right,swappedHost_apply]
 change colorSwap.symm (c (b.marked.vertex 15) (b.left.vertex i))=colorSwap.symm (palette 3) ↔ _
 constructor
 · intro h;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,colorSwap.symm.injective h⟩
 · intro h;exact congrArg colorSwap.symm (Finset.mem_filter.mp h).2

def swapShape : Shape→Shape
 | .freeFour=>.freeFour | .leftFour=>.rightFour | .rightFour=>.leftFour | .allFive=>.allFive

theorem exchange_record {c:Host} {five:Bool} {t:Types} (b:Blocks c ⟨.D,five⟩ t) (s:Shape):
 sourceRecord (exchange b) (swapShape s)=PricingIntegration.PairAdmission.exchange (sourceRecord b s):=by
 unfold sourceRecord PricingIntegration.PairAdmission.exchange
 rw[exchange_left_support,exchange_right_support]
 cases s <;> rfl

/-- Eliminate the sole census exchange by one genuine global recoloring and
whole-neighborhood coordinate change. The mark and full free support survive. -/
theorem actual_pair_admitted {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (hc:NoMonochromaticTriangle c) (sl sr:Bool)
 (hn:CompletionC.CommonSupportNormalization.Normalized b sl sr) (ho:CommonOwner l t):
 ∃σ:FourColor≃FourColor,let d:=relabel c (Equiv.refl _) σ
 NoMonochromaticTriangle d ∧ ∃u:Types,∃z:Blocks d l u,u=t ∧ z.root=b.root ∧
 ∃s:Shape,freeSize l=s.free ∧∃p:Fin 737,PricingIntegration.PairAdmission.retained p=sourceRecord z s:=by
 obtain ⟨s,hf,hl,hr,p,hp,hcase⟩:=normalized_admitted b hc sl sr hn ho
 rcases hcase with he|⟨hD,hL,hR,he⟩
 · exact ⟨Equiv.refl _,hc,t,b,rfl,rfl,s,hf,p,he⟩
 · rcases l with ⟨profile,five⟩
   cases hD
   have ht:swapTypes t=t:=by cases t with | mk a d q=>simp_all[swapTypes]
   refine ⟨colorSwap,swappedHost_good c hc,swapTypes t,exchange b,ht,rfl,swapShape s,?_,p,?_⟩
   · cases s <;> exact hf
   · exact he.trans (exchange_record b s).symm
#print axioms exchange
#print axioms actual_pair_admitted
end CompletionC.CommonExchange
