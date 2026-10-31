import UniformK60.CommonExchange
import UniformK60.NativePairRoleFrame
import UniformK60.NativeCatalogue
set_option autoImplicit false
namespace UniformK60.Common600
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open PricingABD.ABLayout
open PricingIntegration.PairAdmission
open UniformK60.CommonBlocks UniformK60.CommonSupportNormalization UniformK60.CommonPairAdmission
open UniformK60.CommonExchange CompletionC.NativeMatrices UniformK60.NativePairRoleFrame UniformK60.NativeCatalogue

theorem shape_code_injective :Function.Injective Shape.code:=by
 intro a b h;cases a <;> cases b <;> simp_all[Shape.code]

theorem admitted_shape {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s):(pairTable p).shape=s:=by
 apply shape_code_injective
 exact (pair_shape p).trans (congrArg Record.stage hp)

/-- Exhaustive same-host entrance to the native pair and600-word boundary.
All global changes are one palette permutation; only the complete free
support is subsequently reordered by the catalogue theorem. -/
theorem common_to_exact600 {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (hc:NoMonochromaticTriangle c) (ho:CommonOwner l t):
 ∃σ:FourColor≃FourColor,let d:=relabel c (Equiv.refl _) σ
 NoMonochromaticTriangle d ∧ (σ=Equiv.refl _ ∨ σ=colorSwap) ∧ ∃u:Types,∃z:Blocks d l u,u=t ∧ z.root=b.root ∧ z.mark=b.mark ∧
 ∃s:Shape,∃hf:freeSize l=s.free,∃p:Fin 737,∃hp:retained p=sourceRecord z s,
 (pairTable p).shape=s ∧
 ∃perm:Equiv.Perm (Fin s.free),∃i:Fin 600,∀a d':Fin s.dimension,a≠d'→
 d (reorderedVertex s (shapeFrame z s hf p hp) perm a)
   (reorderedVertex s (shapeFrame z s hf p hp) perm d')=
 palette (matrix s (candidate s i) a d'):=by
 obtain ⟨sl,sr,z,hroot,hfree,hmark,hn⟩:=normalize_foreign b hc
 obtain ⟨σ,good,hσ,u,z',hu,hr,hm,s,hf,p,hp⟩:=actual_pair_admitted z hc sl sr hn ho
 refine ⟨σ,good,hσ,u,z',hu,hr.trans hroot,hm.trans hmark,s,hf,p,hp,admitted_shape z' s p hp,?_⟩
 exact actual_catalogue s (shapeFrame z' s hf p hp) good
#print axioms common_to_exact600
end UniformK60.Common600
