import UniformK60.Common600
import UniformK60.NativeSignedSupport
import UniformK60.NativeFreeGeometry
import CompletionC.CommonCases

/-! Actual-host support/word coverage. The marked root cell is not assumed
large or assigned a template at this stage. Every retained positive and
negative foreign-membership fact concerns an actual K60 edge. -/
set_option autoImplicit false
namespace UniformK60.CommonWordCover
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open PricingABD.ABLayout PricingIntegration.PairAdmission CompletionC.NativeMatrices
open UniformK60.CommonBlocks UniformK60.CommonPairAdmission UniformK60.CommonSupportNormalization
open UniformK60.CommonExchange UniformK60.Common600 UniformK60.NativeSelectedBlocks
open UniformK60.NativePhysicalRepresentative UniformK60.NativeSupportIndex
open UniformK60.NativeFreeGeometry UniformK60.NativeSignedSupport

theorem owner_common {l : Layout} {t : Types}
    (h : CompletionC.CommonCases.NativeOwner l t) : CommonOwner l t := by
  cases hp : l.profile <;> simp_all [CompletionC.CommonCases.NativeOwner,CommonOwner]

theorem source_compatible {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (p : Fin 737) (hf : freeSize l=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape) :
    CompletionC.CommonCases.Compatible l t p :=
  ⟨congrArg Record.family hp,congrArg Record.leftKind hp,
    congrArg Record.rightKind hp,hf⟩

/-- A retained pair's whole-block factors realize its exact native word,
its canonical free P4/C5, and all signed foreign support memberships. -/
theorem admitted_pair_realized {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (hc : NoMonochromaticTriangle c) (p : Fin 737)
    (hf : freeSize l=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape) :
    ∃ j : Fin (pairTable p).count, ∃ z : Blocks c l t,
      z.root=b.root ∧ z.mark=b.mark ∧ Geometry t (frame z) ∧
      (∀ a d : Fin (pairTable p).shape.dimension,a≠d →
        c ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp a))
          ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp d))=
          palette (matrix (pairTable p).shape ((pairTable p).representative j) a d)) ∧
      (∀ v : Fin (leftSize l),c z.mark (z.left.vertex v)=palette 3 ↔
        v.val ∈ (retained p).left) ∧
      (∀ v : Fin (rightSize l),c z.mark (z.right.vertex v)=palette 3 ↔
        v.val ∈ (retained p).right) := by
  obtain ⟨perm,i,hmat⟩ := native_representative b hc p hf hp
  let z := selectedBlocks b p hf perm i
  exact ⟨(pairTable p).target i,z,rfl,rfl,
    geometry_of_matrix b z (pairTable p).shape hf p hp _ hmat,hmat,
    left_native_membership b p hf hp perm i,right_native_membership b p hf hp perm i⟩

/-- Complete physical cover of the common A/B/mixed-D foreign owners.
Only the actual mark, complete foreign maps and its full free support are
needed; no host extension and no marked16 premise enters the finite cover. -/
theorem physical_word_cover {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (hc : NoMonochromaticTriangle c)
    (ho : CompletionC.CommonCases.NativeOwner l t) :
    ∃ σ : FourColor ≃ FourColor, let d := relabel c (Equiv.refl _) σ
    NoMonochromaticTriangle d ∧ (σ=Equiv.refl _ ∨ σ=colorSwap) ∧
    ∃ w : Blocks d l t,w.root=b.root ∧ w.mark=b.mark ∧
    ∃ p : Fin 737,CompletionC.CommonCases.Admitted l t p ∧
    ∃ hf : freeSize l=(pairTable p).shape.free,
    ∃ hp : retained p=sourceRecord w (pairTable p).shape,
    ∃ j : Fin (pairTable p).count,∃ z : Blocks d l t,
      z.root=b.root ∧ z.mark=b.mark ∧ Geometry t (frame z) ∧
      (∀ a v : Fin (pairTable p).shape.dimension,a≠v →
        d ((frame z).vertex (supportIndex w (pairTable p).shape hf p hp a))
          ((frame z).vertex (supportIndex w (pairTable p).shape hf p hp v))=
          palette (matrix (pairTable p).shape ((pairTable p).representative j) a v)) ∧
      (∀ v : Fin (leftSize l),d z.mark (z.left.vertex v)=palette 3 ↔
        v.val ∈ (retained p).left) ∧
      (∀ v : Fin (rightSize l),d z.mark (z.right.vertex v)=palette 3 ↔
        v.val ∈ (retained p).right) := by
  obtain ⟨sl,sr,w,hroot,_,hmark,hn⟩ := normalize_foreign b hc
  obtain ⟨σ,good,hσ,u,w',hu,hr,hm,s,hf,p,hp⟩ :=
    actual_pair_admitted w hc sl sr hn (owner_common ho)
  subst u
  have he := admitted_shape w' s p hp
  cases he
  obtain ⟨j,z,hzr,hzm,hg,hmat,hl,hrr⟩ := admitted_pair_realized w' good p hf hp
  exact ⟨σ,good,hσ,w',hr.trans hroot,hm.trans hmark,p,
    ⟨ho,source_compatible w' p hf hp⟩,hf,hp,j,z,
    hzr.trans (hr.trans hroot),hzm.trans (hm.trans hmark),hg,hmat,hl,hrr⟩

#print axioms physical_word_cover
end UniformK60.CommonWordCover
