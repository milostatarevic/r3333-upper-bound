import UniformK61.CommonSoundness
import CompletionC.CommonCases
import CompletionC.NativeSignedSupport
import CompletionC.NativeFreeGeometry
import CompletionC.CommonEntrance

set_option autoImplicit false
namespace UniformK61.CommonCover
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter Ramsey61.CPhysicalNormalization
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.CommonSupportNormalization CompletionC.CommonExchange CompletionC.Common600
open CompletionC.NativePhysicalRepresentative CompletionC.NativeSelectedBlocks
open CompletionC.NativeFreeGeometry CompletionC.NativeSignedSupport CompletionC.CommonCases
open UniformK61.CommonHost UniformK61.CommonFormula UniformK61.CommonSoundness

/-- The finite profile, template, support-pair and word index set. -/
abbrev Case := CompletionC.CommonCases.Case

def formula (k : Case) : CNF :=
  CommonFormula.formula k.1 k.2.1 k.2.2.1.val k.2.2.2

/-- Normalized blocks and their selected word determine signed facts in
one physical coloring on all 61 vertices. -/
theorem admitted_pair_satisfiable {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (hc : NoMonochromaticTriangle c) (p : Fin 737)
    (hf : freeSize l=(pairTable p).shape.free)
    (hp : PricingIntegration.PairAdmission.retained p=sourceRecord b (pairTable p).shape) :
    ∃j : Fin (pairTable p).count,∃w : Valuation,
      FormulaSat w (CommonFormula.formula l t p j) := by
  obtain ⟨perm,i,hmat⟩ := native_representative b hc p hf hp
  let z := selectedBlocks b p hf perm i
  have hg := geometry_of_matrix b z (pairTable p).shape hf p hp
    ((pairTable p).representative ((pairTable p).target i)) hmat
  have hl := left_native_membership b p hf hp perm i
  have hr := right_native_membership b p hf hp perm i
  have hu : Core.UnitsMatch (coloring z) (units l t p ((pairTable p).target i)) := by
    intro u hu
    simp only [units,List.mem_append] at hu
    rcases hu with (((h|h)|h)|h)|h
    · exact spokes_match z u h
    · exact templates_match z u h
    · exact free_match z hg u h
    · exact word_match b z p hf hp _ hmat u h
    · exact membership_match z hc p hl hr u h
  exact ⟨(pairTable p).target i,Core.physicalValuation (coloring z),
    Core.coloring_satisfies_formula (coloring z) (coloring_good z hc) _ hu⟩

/-- Complete same-host A/B/mixed-D cover, including the entire low-cell
membership supplied by CommonHost. -/
theorem physical_common_cover {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (hc : NoMonochromaticTriangle c) (ho : NativeOwner l t) :
    ∃p : Fin 737,Admitted l t p ∧ ∃j : Fin (pairTable p).count,∃w : Valuation,
      FormulaSat w (CommonFormula.formula l t p j) := by
  obtain ⟨sl,sr,z,_,_,_,hn⟩ := normalize_foreign b hc
  obtain ⟨σ,good,u,z',hu,_,s,hf,p,hp⟩ := actual_pair_admitted z hc sl sr hn (owner_common ho)
  subst u
  have he := admitted_shape z' s p hp
  cases he
  exact ⟨p,⟨ho,source_compatible z' p hf hp⟩,admitted_pair_satisfiable z' good p hf hp⟩

theorem actual_A_cover (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=48) (hh : 48≤H c r) : ∃k : Case,∃w : Valuation,FormulaSat w (formula k) := by
  obtain ⟨σ,good,_,_,five,t,b,_,h01,h12⟩ := CompletionC.CommonEntrance.actual_A c hc r hw hh
  obtain ⟨p,hp,j,w,hs⟩ := physical_common_cover b good ⟨h01,h12⟩
  exact ⟨⟨⟨.A,five⟩,t,⟨p,hp⟩,j⟩,w,hs⟩

theorem actual_B_cover (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=47) (hh : 47≤H c r) : ∃k : Case,∃w : Valuation,FormulaSat w (formula k) := by
  obtain ⟨σ,good,_,_,five,t,b,_,ht⟩ := CompletionC.CommonEntrance.actual_B c hc r hw hh
  obtain ⟨p,hp,j,w,hs⟩ := physical_common_cover b good ht
  exact ⟨⟨⟨.B,five⟩,t,⟨p,hp⟩,j⟩,w,hs⟩

theorem actual_D_cover_or_UU (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hw : W c r=46) (hh : 46≤H c r) :
    ∃σ : FourColor≃FourColor,let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ ∃five : Bool,∃t : Types,∃b : Blocks d ⟨.D,five⟩ t,
      b.root=r ∧ ((t.left=false ∧ t.right=false) ∨
        ∃k : Case,∃w : Valuation,FormulaSat w (formula k)) := by
  obtain ⟨σ,good,_,five,t,b,hr,ho⟩ := CompletionC.CommonEntrance.actual_D c hc r hw hh
  refine ⟨σ,good,five,t,b,hr,?_⟩
  cases ht : t.right with
  | false => left;exact ⟨ho.resolve_right (by simp [ht]),rfl⟩
  | true =>
    right
    obtain ⟨p,hp,j,w,hs⟩ := physical_common_cover b good ht
    exact ⟨⟨⟨.D,five⟩,t,⟨p,hp⟩,j⟩,w,hs⟩

#print axioms admitted_pair_satisfiable
#print axioms physical_common_cover
#print axioms actual_A_cover
#print axioms actual_B_cover
#print axioms actual_D_cover_or_UU
end UniformK61.CommonCover
