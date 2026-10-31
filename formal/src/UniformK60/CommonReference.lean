import UniformK60.CommonCoordinates
import CompletionC.SupportEdges
import UniformK60.NativeSupportIndex

/-! The61-position reference is only a coordinate device. Restricting it is
exactly the physical K60 coloring; goodness is asserted only there. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.CommonReference
open Ramsey61 UniformK60.Physical UniformK60.CommonHost
open UniformK60.CommonCoordinates UniformK60.UnitRestriction
open PricingABD.ABLayout UniformK60.CommonBlocks
open PricingIntegration.PairAdmission CompletionC.NativeMatrices
open UniformK60.CommonPairAdmission UniformK60.NativeSupportIndex

variable {c : Host} {l : Layout} {t : Types} {missing : Missing}

noncomputable def referenceMap (b : Blocks c l t) (h : Completion b missing)
    (v : Fin 61) : Vertex := fullMap b h ((omission l missing).predAbove v)

noncomputable def referenceColoring (b : Blocks c l t) (h : Completion b missing) :
    ReferenceColoring where
  color u v := c (referenceMap b h u) (referenceMap b h v)
  color_symm _ _ := c.color_symm _ _

@[simp] theorem reference_restrict (b : Blocks c l t) (h : Completion b missing) :
    restrictColoring (referenceColoring b h) (omission l missing)=coloring b h := by
  ext a v <;> simp [restrictColoring,referenceColoring,referenceMap,coloring,
    Fin.predAbove_succAbove]

theorem reference_restrict_good (b : Blocks c l t) (h : Completion b missing)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (restrictColoring (referenceColoring b h) (omission l missing)) := by
  rw [reference_restrict]
  exact coloring_good b h hc

@[simp] theorem referenceMap_root (b : Blocks c l t) (h : Completion b missing) :
    referenceMap b h 0=b.root := by rw [referenceMap,deleted_root,fullMap_root]

@[simp] theorem referenceMap_mark (b : Blocks c l t) (h : Completion b missing) :
    referenceMap b h 60=b.mark := by rw [referenceMap,deleted_mark,fullMap_mark]

@[simp] theorem referenceMap_low (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (lowSize l)) (hi : Reference.low l i≠(omission l missing).castSucc) :
    referenceMap b h (Reference.low l i)=lowMap b h (lowIndex l missing i hi) := by
  rw [referenceMap,deleted_low l missing i hi,fullMap_low]

@[simp] theorem referenceMap_left (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (leftSize l)) : referenceMap b h (Reference.left l i)=b.left.vertex i := by
  rw [referenceMap,deleted_left,fullMap_left]

@[simp] theorem referenceMap_right (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (rightSize l)) : referenceMap b h (Reference.right l i)=b.right.vertex i := by
  rw [referenceMap,deleted_right,fullMap_right]

@[simp] theorem referenceMap_marked (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (markedSize missing)) :
    referenceMap b h (Reference.marked l (markedPosition missing i))=h.marked.vertex i := by
  rw [referenceMap,deleted_marked,fullMap_marked]

@[simp] theorem referenceMap_free (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (freeSize l)) :
    referenceMap b h (UniformK61.CommonHost.retain l (PricingABD.ABLayout.free l i))=b.free i := by
  rw [referenceMap,deleted_free,fullMap_low,low_initial]

/-- The coordinate equality is independent of the physical host size. -/
theorem label_supportIndex {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (p : Fin 737) (hf : freeSize l=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape)
    (a : Fin (pairTable p).shape.dimension) :
    CompletionC.SupportEdges.label l p a.val=
      (supportIndex b (pairTable p).shape hf p hp a).val := by
  unfold CompletionC.SupportEdges.label supportIndex
  by_cases h0 : a.val<(pairTable p).shape.free
  · simp only [if_pos h0,dif_pos h0];rfl
  · simp only [if_neg h0,dif_neg h0]
    by_cases h1 : a.val<(pairTable p).shape.free+(pairTable p).shape.left
    · simp only [if_pos h1,dif_pos h1];rfl
    · simp only [if_neg h1,dif_neg h1];rfl

theorem referenceMap_support {c : Host} {l : Layout} {t : Types}
    (b z : Blocks c l t) (h : Completion z missing)
    (p : Fin 737) (hf : freeSize l=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape)
    (a : Fin (pairTable p).shape.dimension) :
    referenceMap z h (UniformK61.CommonHost.retain l
      (supportIndex b (pairTable p).shape hf p hp a))=
      (frame z).vertex (supportIndex b (pairTable p).shape hf p hp a) := by
  unfold supportIndex
  split_ifs
  · rw [referenceMap_free]
    exact (physical_free z _).symm
  · rw [UniformK61.CommonHost.retain_left,referenceMap_left]
    exact (physical_left z _).symm
  · rw [UniformK61.CommonHost.retain_right,referenceMap_right]
    exact (physical_right z _).symm

#print axioms reference_restrict_good
end UniformK60.CommonReference
