import UniformK60.CommonShapes
import UniformK60.NativeCatalogue
import UniformK61.UUPureCoordinates

set_option autoImplicit false
namespace UniformK60.UUPhysicalCover
open Ramsey61 Finset UniformK60.Physical
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open UniformK60.CommonBlocks UniformK60.CommonSupportNormalization UniformK60.CommonShapes
open CompletionC.NativeMatrices UniformK60.NativeCatalogue
open UniformK60.ClassificationSupports UniformK60.ClassificationGeometry
open PricingIntegration.PairAdmission
open UniformK61.UUSupportData UniformK61.UUPureCoordinates
variable {c : Host} {five : Bool}

private theorem reps_iff (s : Finset (Fin 15)) (small : Bool) (n : Nat)
    (hn : (if small then 4 else 5)=n) : naturalSet s∈reps 0 small ↔ s∈supports n := by
  unfold reps
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp h
    have hzs : z=s := naturalSet_injective he
    subst z
    cases small <;> subst n <;> simpa [supports] using hz
  · intro h
    apply List.mem_map.mpr
    refine ⟨s,?_,rfl⟩
    cases small <;> subst n <;> simpa [supports] using h

/-- Independently normalized complete U15 cells give one of the 66 support
pairs. This retains the full host and the exact low-cell marked support. -/
theorem normalized_pair (q : Bool) (b : Blocks c ⟨.D,five⟩ ⟨false,false,q⟩)
    (hc : NoMonochromaticTriangle c) :
    ∃p : Pair,∃z : Blocks c (layout p) ⟨false,false,q⟩,
      z.root=b.root ∧ z.mark=b.mark ∧
      support (side:=false) z.left (z.mark)=leftSet p ∧
      support (side:=true) z.right (z.mark)=rightSet p := by
  obtain ⟨sl,sr,z,hroot,_,hmark,hn⟩ := normalize_foreign b hc
  obtain ⟨s,hf,hl,hr⟩ := normalized_shape z hc sl sr hn
  have hleft : support (side:=false) z.left (z.mark)∈supports s.left := by
    apply (reps_iff _ sl s.left hl).mp
    exact hn.2.2.1
  have hright : support (side:=true) z.right (z.mark)∈supports s.right := by
    apply (reps_iff _ sr s.right hr).mp
    exact hn.2.2.2
  obtain ⟨p,hp,hpl,hpr⟩ := pairs_cover s _ hleft _ hright
  have hfive : five=UniformK61.UUSupportData.five p := by
    unfold UniformK61.UUSupportData.five
    rw [hp]
    cases five <;> cases s <;> simp_all [freeSize,Shape.free]
  subst five
  exact ⟨p,z,hroot,hmark,hpl.symm,hpr.symm⟩

noncomputable def supportFrame (q : Bool) (p : Pair)
    (b : Blocks c (layout p) ⟨false,false,q⟩)
    (hl : support (side:=false) b.left (b.mark)=leftSet p)
    (hr : support (side:=true) b.right (b.mark)=rightSet p) :
    UniformK60.ThreeSupportFrame.Frame c (shape p).free (shape p).left (shape p).right where
  root := b.root
  mark := b.mark
  free := (finCongr (layout_free p).symm).toEmbedding.trans b.free
  left := (leftEmbedding p).trans b.left.vertex
  right := (rightEmbedding p).trans b.right.vertex
  mark_mem := b.mark_mem
  free_mem i := b.free_mem _
  left_mem i := b.left.mem_neighborhood _
  right_mem i := b.right.mem_neighborhood _
  marked_free i := b.free_own _
  marked_left i := by
    have h : leftOrder p i∈support (side:=false) b.left (b.mark) := by
      rw [hl];exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    exact (mem_filter.mp h).2
  marked_right i := by
    have h : rightOrder p i∈support (side:=true) b.right (b.mark) := by
      rw [hr];exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    exact (mem_filter.mp h).2
  left_edges a d had := by
    change c (b.left.vertex (leftOrder p a)) (b.left.vertex (leftOrder p d))=_
    erw [b.left.map_color _ _ ((orders_ok p).1.ne had),b.left_palette]
    change palette (PricingIntegration.BActualFrame.foreign 1
      (R4333.k15Untwisted (leftOrder p a) (leftOrder p d)))=_
    rw [(orders_ok p).2.2.1 a d had]
    split_ifs <;> rfl
  right_edges a d had := by
    change c (b.right.vertex (rightOrder p a)) (b.right.vertex (rightOrder p d))=_
    erw [b.right.map_color _ _ ((orders_ok p).2.1.ne had),b.right_palette]
    change palette (PricingIntegration.BActualFrame.foreign 2
      (R4333.k15Untwisted (rightOrder p a) (rightOrder p d)))=_
    rw [(orders_ok p).2.2.2 a d had]
    split_ifs <;> rfl

/-- Actual support extraction reaches a published native600 matrix by
reordering only the actual free support. No extra vertex is introduced. -/
theorem actual_UU_matrix (q : Bool)
    (b : Blocks c ⟨.D,five⟩ ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c) :
    ∃ p : Pair, ∃ z : Blocks c (layout p) ⟨false,false,q⟩,
    z.root=b.root ∧ z.mark=b.mark ∧
    ∃ hl : support (side:=false) z.left z.mark = leftSet p,
    ∃ hr : support (side:=true) z.right z.mark = rightSet p,
    ∃ perm : Equiv.Perm (Fin (shape p).free), ∃ i : Fin 600,
    ∀ a d : Fin (shape p).dimension, a ≠ d →
      c (reorderedVertex (shape p) (supportFrame q p z hl hr) perm a)
        (reorderedVertex (shape p) (supportFrame q p z hl hr) perm d) =
      palette (matrix (shape p) (candidate (shape p) i) a d) := by
  obtain ⟨p,z,hroot,hmark,hl,hr⟩ := normalized_pair q b hc
  obtain ⟨perm,i,hmat⟩ := actual_catalogue (shape p) (supportFrame q p z hl hr) hc
  exact ⟨p,z,hroot,hmark,hl,hr,perm,i,hmat⟩

#print axioms normalized_pair
#print axioms supportFrame
#print axioms actual_UU_matrix
end UniformK60.UUPhysicalCover
