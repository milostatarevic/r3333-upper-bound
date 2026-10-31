import UniformK60.UUPhysicalCover
import UniformK60.CommonReference

set_option autoImplicit false
namespace UniformK60.UUCoordinates
open Ramsey61 Finset UniformK60.Physical
open PricingABD PricingABD.ABLayout
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonReference
open UniformK60.ClassificationSupports UniformK60.UUPhysicalCover
open UniformK60.NativeCatalogue CompletionC.NativeMatrices
open UniformK61.UUSupportData UniformK61.UUPureCoordinates

variable {c : Host}

noncomputable def reorderFree {l : Layout} {t : Types} (b : Blocks c l t)
    (perm : Equiv.Perm (Fin (freeSize l))) : Blocks c l t :=
  { b with
    free := perm.toEmbedding.trans b.free
    free_mem i := b.free_mem _
    free_own i := b.free_own _
    free_exact v := by
      rw [b.free_exact]
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨perm.symm i,congrArg b.free (perm.apply_symm_apply i)⟩
      · rintro ⟨i,rfl⟩
        exact ⟨perm i,rfl⟩ }

noncomputable def freePermutation (p : Pair) (perm : Equiv.Perm (Fin (shape p).free)) :
    Equiv.Perm (Fin (freeSize (layout p))) :=
  (finCongr (layout_free p)).trans (perm.trans (finCongr (layout_free p).symm))

theorem matrix_vertex (q : Bool) (p : Pair) (b : Blocks c (layout p) ⟨false,false,q⟩)
    (hl : support (side:=false) b.left b.mark=leftSet p)
    (hr : support (side:=true) b.right b.mark=rightSet p)
    (perm : Equiv.Perm (Fin (shape p).free)) {missing : Missing}
    (h : Completion (reorderFree b (freePermutation p perm)) missing)
    (a : Fin (shape p).dimension) :
    referenceMap (reorderFree b (freePermutation p perm)) h (UniformK61.UUSourceDefs.matrixVertex p a)=
      reorderedVertex (shape p) (supportFrame q p b hl hr) perm a := by
  rw [reorderedVertex_formula]
  unfold UniformK61.UUSourceDefs.matrixVertex
  split_ifs with h0 h1
  · have hf : a.val<freeSize (layout p) := by rw [layout_free];exact h0
    have he : (⟨a.val+1,by
          have h : (shape p).free≤5 := by cases shape p <;> decide
          omega⟩ : Fin 61)=
        UniformK61.CommonHost.retain (layout p)
          (ABLayout.free (layout p) ⟨a.val,hf⟩) := by
      rw [UniformK61.CommonHost.retain_free]
      apply Fin.ext
      dsimp [UniformK61.CommonHost.lowVertex]
      omega
    rw [he,referenceMap_free]
    rfl
  · change referenceMap (reorderFree b (freePermutation p perm)) h
        (CommonCoordinates.Reference.left (layout p)
          (leftOrder p ⟨a.val-(shape p).free,by omega⟩))=_
    rw [referenceMap_left]
    rfl
  · change referenceMap (reorderFree b (freePermutation p perm)) h
        (CommonCoordinates.Reference.right (layout p)
          (rightOrder p ⟨a.val-(shape p).free-(shape p).left,by
            have h:=Shape.dimension_sum (shape p);have ha:=a.isLt;omega⟩))=_
    rw [referenceMap_right]
    rfl

theorem matrix_vertex_ne_fourteen (p : Pair) (a : Fin (shape p).dimension) :
    UniformK61.UUSourceDefs.matrixVertex p a ≠ 14 := by
  have hf : (shape p).free≤5 := by cases shape p <;> decide
  unfold UniformK61.UUSourceDefs.matrixVertex
  split_ifs with h0 h1
  · intro he
    have hh:=congrArg Fin.val he
    change a.val+1=14 at hh
    omega
  · intro he
    have hh:=congrArg Fin.val he
    dsimp [UniformK61.UUSourceDefs.leftVertex] at hh
    omega
  · intro he
    have hh:=congrArg Fin.val he
    dsimp [UniformK61.UUSourceDefs.rightVertex] at hh
    omega

#print axioms matrix_vertex
end UniformK60.UUCoordinates
