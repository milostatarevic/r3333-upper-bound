import CompletionC.CommonShapes
import PricingIntegration.PairAdmissionHeaders
import PricingIntegration.PairNativeBindingComplete
set_option autoImplicit false
namespace CompletionC.CommonPairAdmission
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout
open PricingIntegration.PhysicalForeignSupport PricingIntegration.PairAdmission
open CompletionC.CommonBlocks CompletionC.CommonSupportNormalization CompletionC.NativeMatrices

def familyCode : Profile→Nat | .A=>0 | .B=>1 | .D=>2
/-- Exactly the common route's native foreign owners; D U/U is deliberately
outside this boundary and keeps its separate679-leaf construction. -/
def CommonOwner (l:Layout) (types:Types):Prop:=
 match l.profile with
 | .A=>types.left=false∨types.right=true
 | .B=>True
 | .D=>types.right=true

theorem native_header {l:Layout} {types:Types} (h:CommonOwner l types):
 (familyCode l.profile,kindCode (leftLarge l) types.left,kindCode (rightLarge l) types.right)∈nativeHeaderKinds:=by
 rcases l with ⟨profile,five⟩
 rcases types with ⟨a,b,q⟩
 cases profile <;> cases a <;> cases b <;>
 simp_all [CommonOwner,nativeHeaderKinds,familyCode,kindCode,leftLarge,rightLarge]

def sourceRecord {c:Host} {l:Layout} {types:Types} (b:Blocks c l types) (s:Shape):Record:=
 ⟨familyCode l.profile,kindCode (leftLarge l) types.left,kindCode (rightLarge l) types.right,s.code,
 naturalSet (support (side:=false) b.left (b.marked.vertex 15)),
 naturalSet (support (side:=true) b.right (b.marked.vertex 15))⟩

theorem normalized_admitted {c:Host} {l:Layout} {types:Types} (b:Blocks c l types)
 (hc:NoMonochromaticTriangle c) (sl sr:Bool) (hn:Normalized b sl sr)
 (ho:CommonOwner l types):
 ∃s:Shape,freeSize l=s.free ∧ (if sl then 4 else 5)=s.left ∧ (if sr then 4 else 5)=s.right ∧
 ∃p:Fin 737,NativeBinding p ∧
 (retained p=sourceRecord b s ∨
 (l.profile=.D ∧ types.left=true ∧ types.right=true ∧ retained p=exchange (sourceRecord b s))):=by
 obtain ⟨s,hf,hl,hr⟩:=CompletionC.CommonShapes.normalized_shape b hc sl sr hn
 have hsl:(s.code==1)=sl:=by cases s <;> cases sl <;> simp_all[Shape.left,Shape.code]
 have hsr:(s.code==2)=sr:=by cases s <;> cases sr <;> simp_all[Shape.right,Shape.code]
 have hb:s.code<4:=by cases s <;> decide
 obtain ⟨rowid,hrow⟩:=native_header_present _ _ _ ⟨s.code,hb⟩ (native_header ho)
 have hleft:naturalSet (support (side:=false) b.left (b.marked.vertex 15))∈reps (row rowid).leftKind ((row rowid).stage==1):=by
  rw[hrow];simpa only[hsl] using hn.2.2.1
 have hright:naturalSet (support (side:=true) b.right (b.marked.vertex 15))∈reps (row rowid).rightKind ((row rowid).stage==2):=by
  rw[hrow];simpa only[hsr] using hn.2.2.2
 obtain ⟨p,hp,hadmit⟩:=native_support_product_admitted rowid _ _ hleft hright
 rw[hrow] at hadmit
 refine ⟨s,hf,hl,hr,p,hp,?_⟩
 rcases hadmit with he|⟨hD,hL,hR,he⟩
 · exact Or.inl he
 · right
   have hd:l.profile=.D:=by cases hh:l.profile <;> simp_all[familyCode]
   have hleft':types.left=true:=by rw[hd] at hL;cases hh:types.left <;> simp_all[kindCode,leftLarge]
   have hright':types.right=true:=by rw[hd] at hR;cases hh:types.right <;> simp_all[kindCode,rightLarge]
   exact ⟨hd,hleft',hright',he⟩
#print axioms normalized_admitted
end CompletionC.CommonPairAdmission
