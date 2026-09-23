import CompletionC.NativePrefix
import CompletionC.Common600
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativeFamilyJoin
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingABD.ABLayout PricingIntegration.PairAdmission
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.CommonSupportNormalization
open CompletionC.CommonExchange CompletionC.Common600 CompletionC.NativeMatrices
open CompletionC.NativeSelectedBlocks CompletionC.NativeSupportIndex CompletionC.NativePhysicalRepresentative
open CompletionC.NativeFreeGeometry CompletionC.NativeSignedSupport CompletionC.NativeSuffixSat

def NativeOwner (l:Layout) (t:Types):Prop:=
 match l.profile with
 | .A=>(t.left=false∨t.right=true) ∧(t.right=false∨t.marked=true)
 | .B=>t.right=false∨t.marked=true
 | .D=>t.right=true

def Compatible (l:Layout) (t:Types) (p:Fin 737):Prop:=
 (retained p).family=familyCode l.profile ∧
 (retained p).leftKind=kindCode (leftLarge l) t.left ∧
 (retained p).rightKind=kindCode (rightLarge l) t.right ∧
 freeSize l=(pairTable p).shape.free

def Admitted (l:Layout) (t:Types) (p:Fin 737):Prop:=NativeOwner l t ∧Compatible l t p

def formula (l:Layout) (t:Types) (p:Fin 737) (j:Fin (pairTable p).count):CNF:=
 CompletionC.NativePrefix.formula l t ++CompletionC.NativeSuffix.formula l p j

theorem owner_common {l:Layout} {t:Types} (h:NativeOwner l t):CommonOwner l t:=by
 cases hp:l.profile <;> simp_all[NativeOwner,CommonOwner]

theorem source_compatible {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape):Compatible l t p:=
 ⟨congrArg Record.family hp,congrArg Record.leftKind hp,congrArg Record.rightKind hp,hf⟩

/-- Actual complete blocks reaching a retained pair satisfy one of that
pair's exact original prefix-plus-signed-suffix formulas. -/
theorem admitted_pair_satisfiable {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (hc:NoMonochromaticTriangle c) (p:Fin 737)
 (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape):
 ∃j:Fin (pairTable p).count,∃w:Valuation,FormulaSat w (formula l t p j):=by
 obtain ⟨perm,i,hmat⟩:=native_representative b hc p hf hp
 let z:=selectedBlocks b p hf perm i
 have hg:=geometry_of_matrix b z (pairTable p).shape hf p hp
  ((pairTable p).representative ((pairTable p).target i)) hmat
 obtain ⟨w,hprefix,hedges⟩:=CompletionC.NativePrefix.actual_prefix t (frame z) hc hg
 have hsuffix:=suffix_sat b z p hf hp ((pairTable p).target i) w hedges
  (left_native_membership b p hf hp perm i) (right_native_membership b p hf hp perm i) hmat
 refine ⟨(pairTable p).target i,w,?_⟩
 intro clause hm
 rcases List.mem_append.mp hm with hm|hm
 · exact hprefix clause hm
 · exact hsuffix clause hm

/-- Complete common A/B/mixed-D physical cover, with no root, support,
case-orbit, matrix, valuation or encoding assumptions left unproved. -/
theorem common_native_cover {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (hc:NoMonochromaticTriangle c) (ho:NativeOwner l t):
 ∃p:Fin 737,Admitted l t p ∧∃j:Fin (pairTable p).count,∃w:Valuation,FormulaSat w (formula l t p j):=by
 obtain ⟨sl,sr,z,_,_,_,hn⟩:=normalize_foreign b hc
 obtain ⟨σ,good,u,z',hu,_,s,hf,p,hp⟩:=actual_pair_admitted z hc sl sr hn (owner_common ho)
 subst u
 have he:=admitted_shape z' s p hp
 cases he
 refine ⟨p,⟨ho,source_compatible z' p hf hp⟩,?_⟩
 exact admitted_pair_satisfiable z' good p hf hp
#print axioms admitted_pair_satisfiable
#print axioms common_native_cover
end CompletionC.NativeFamilyJoin
