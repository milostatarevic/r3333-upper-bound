import UniformK61.CEntranceSoundness
set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingIntegration.PairAdmission
open CompletionC.CommonSupportNormalization CompletionC.NativeMatrices

/-- Exact finite pair metadata of a C entrance. Family0 selects the shared
(16,16) support table and is not a mathematical root-profile assumption. -/
def Compatible (five lt rt : Bool) (p : Fin 737) : Prop :=
  Ordered lt rt ∧ (retained p).family=0 ∧
  (retained p).leftKind=kindCode true lt ∧
  (retained p).rightKind=kindCode true rt ∧
  freeSize five=(pairTable p).shape.free

theorem admitted_shape {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (s : Shape) (p : Fin 737) (hp : retained p=sourceRecord b s) : (pairTable p).shape=s := by
  have hi : Function.Injective Shape.code := by
    intro a b h
    cases a <;> cases b <;> simp_all [Shape.code]
  apply hi
  exact (pair_shape p).trans (congrArg Record.stage hp)

/-- A C14 mark enters the complete finite pair/word boundary using only
its two actual foreign critical cells and exact signed support membership. -/
theorem physical_cover {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (hc : NoMonochromaticTriangle c) (ho : Ordered lt rt) :
    ∃ p : Fin 737, Compatible five lt rt p ∧
      ∃ j : Fin (pairTable p).count, ∃ w : Valuation,
        FormulaSat w (Formula.formula five lt rt p j) := by
  obtain ⟨sl,sr,z,_,_,hn⟩ := normalize_foreign b hc
  obtain ⟨s,hf,_,_,p,_,hp⟩ := normalized_admitted z hc sl sr hn ho
  have he := admitted_shape z s p hp
  cases he
  refine ⟨p,⟨ho,?_,?_,?_,hf⟩,admitted_pair_satisfiable z hc p hf hp⟩
  · exact congrArg Record.family hp
  · exact congrArg Record.leftKind hp
  · exact congrArg Record.rightKind hp

/-- The actual C exterior witness forces a satisfying assignment of one
of the direct full-host formulas. No order-fourteen extension premise is
used, and all marked-neighborhood nonmembers are fixed negatively. -/
theorem actual_C_cover_raw (c : Host) (hc : NoMonochromaticTriangle c)
    (witness : CExteriorWitness c) :
    ∃ five lt rt : Bool, ∃ p : Fin 737, Compatible five lt rt p ∧
      ∃ j : Fin (pairTable p).count, ∃ w : Valuation,
        FormulaSat w (Formula.formula five lt rt p j) := by
  obtain ⟨σ,good,⟨e⟩⟩ := actual_entrance c hc witness
  obtain ⟨five,lt,rt,⟨b⟩⟩ := entrance_has_blocks e good
  obtain ⟨d,hd,l,r,ho,⟨z⟩⟩ := ordered_blocks b good
  obtain ⟨p,hp,j,w,hs⟩ := physical_cover z hd ho
  exact ⟨five,l,r,p,hp,j,w,hs⟩

#print axioms actual_C_cover_raw
end UniformK61.CEntrance
