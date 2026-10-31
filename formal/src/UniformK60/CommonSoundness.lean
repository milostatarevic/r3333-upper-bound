import UniformK60.CommonReference
import UniformK60.NativeFreeGeometry
import UniformK61.CommonSoundness
import UniformK60.ReferenceSource

/-! Every retained archived fact is proved on one actual K60 placement.
Facts incident to the omitted reference position are never assumed. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.CommonSoundness
open Ramsey61 UniformK60.Physical UniformK60.CommonHost UniformK60.CommonCoordinates
open UniformK60.CommonReference UniformK60.UnitRestriction
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open UniformK60.CommonBlocks UniformK60.CommonPairAdmission CompletionC.NativeMatrices
open UniformK60.NativeSupportIndex CompletionC.SupportEdges
open UniformK61.CommonFormula

variable {c : Host} {l : Layout} {t : Types} {missing : Missing}

abbrev Retained (l : Layout) (missing : Missing) (u : UniformK61.Core.PhysicalUnit) :=
  survives (omission l missing) (ReferenceSource.unit u)


private theorem native_palette (own : Fin 4) (q : Fin 3) :
    (UniformK60.PhysicalHelpers.foreignEquiv own q).val=
      palette (PricingABD.ABGeometry.foreign own q) := by
  fin_cases own <;> fin_cases q <;> rfl

private theorem foreign_same (own : Fin 4) (q : Fin 3) :
    UniformK60.PhysicalHelpers.foreign own q=PricingABD.ABGeometry.foreign own q := by
  fin_cases own <;> fin_cases q <;> rfl

theorem spokes_match (b : Blocks c l t) (h : Completion b missing)
    (u : UniformK61.Core.PhysicalUnit) (hu : u ∈ spokes l) (hs : Retained l missing u) :
    UniformK61.Core.UnitMatches (referenceColoring b h) u := by
  simp only [spokes,List.mem_append] at hu
  rcases hu with ((hu|hu)|hu)|hu
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [UniformK61.CommonHost.lowVertex] at this;omega
    · change c (referenceMap b h 0) (referenceMap b h (Reference.low l i))=palette 0
      rw [referenceMap_root,referenceMap_low b h i hs.2]
      exact ((mem_colorNeighborhood _ _ _ _).mp (low_mem b h _)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [UniformK61.CommonHost.leftVertex] at this;omega
    · change c (referenceMap b h 0) (referenceMap b h (Reference.left l i))=palette 1
      rw [referenceMap_root,referenceMap_left]
      exact ((mem_colorNeighborhood _ _ _ _).mp (b.left.mem_neighborhood i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [UniformK61.CommonHost.rightVertex] at this;omega
    · change c (referenceMap b h 0) (referenceMap b h (Reference.right l i))=palette 2
      rw [referenceMap_root,referenceMap_right]
      exact ((mem_colorNeighborhood _ _ _ _).mp (b.right.mem_neighborhood i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [UniformK61.CommonHost.markedVertex] at this;omega
    · obtain ⟨j,hj⟩ := marked_preimage l missing i hs.2
      change c (referenceMap b h 0) (referenceMap b h (Reference.marked l i))=palette 3
      rw [←hj,referenceMap_root,referenceMap_marked]
      exact ((mem_colorNeighborhood _ _ _ _).mp (h.marked.mem_neighborhood j)).2

theorem edge_match (b : Blocks c l t) (h : Completion b missing)
    (a d : Fin (vertexCount l)) (q : Color) (hne : a≠d)
    (he : c (referenceMap b h (UniformK61.CommonHost.retain l a))
      (referenceMap b h (UniformK61.CommonHost.retain l d))=palette q) :
    UniformK61.Core.UnitMatches (referenceColoring b h) (edgeUnit l (a,d,q)) :=
  ⟨(UniformK61.CommonHost.retain_injective l).ne hne,he⟩

theorem templates_match (b : Blocks c l t) (h : Completion b missing)
    (u : UniformK61.Core.PhysicalUnit) (hu : u ∈ templates l t) (hs : Retained l missing u) :
    UniformK61.Core.UnitMatches (referenceColoring b h) u := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hu
  simp only [templateEdges,List.mem_append] at he
  rcases he with (he|he)|he
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp he
    apply edge_match b h _ _ _ ((ABLayout.left_injective l).ne (UniformK61.CommonSoundness.ordered_ne ab hab))
    rw [UniformK61.CommonHost.retain_left,UniformK61.CommonHost.retain_left,
      referenceMap_left,referenceMap_left,b.left.map_color _ _ (UniformK61.CommonSoundness.ordered_ne ab hab),
      b.left_palette,native_palette]
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp he
    apply edge_match b h _ _ _ ((ABLayout.right_injective l).ne (UniformK61.CommonSoundness.ordered_ne ab hab))
    rw [UniformK61.CommonHost.retain_right,UniformK61.CommonHost.retain_right,
      referenceMap_right,referenceMap_right,b.right.map_color _ _ (UniformK61.CommonSoundness.ordered_ne ab hab),
      b.right_palette,native_palette]
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp he
    have ha := hs.1
    have hb := hs.2
    change UniformK61.CommonHost.retain l (ABLayout.marked l ab.1)≠_ at ha
    change UniformK61.CommonHost.retain l (ABLayout.marked l ab.2)≠_ at hb
    rw [UniformK61.CommonHost.retain_marked] at ha hb
    obtain ⟨a,ha'⟩ := marked_preimage l missing ab.1 ha
    obtain ⟨d,hd'⟩ := marked_preimage l missing ab.2 hb
    have had : a≠d := by intro he;apply UniformK61.CommonSoundness.ordered_ne ab hab;rw [←ha',←hd',he]
    apply edge_match b h _ _ _ ((ABLayout.marked_injective l).ne (UniformK61.CommonSoundness.ordered_ne ab hab))
    rw [UniformK61.CommonHost.retain_marked,UniformK61.CommonHost.retain_marked,
      ←ha',←hd',referenceMap_marked,referenceMap_marked,h.marked.map_color a d had,
      foreign_same]

theorem free_match (b : Blocks c l t) (h : Completion b missing)
    (hg : CommonBlocks.Geometry t (frame b)) :
    ∀ u ∈ freeShape l,UniformK61.Core.UnitMatches (referenceColoring b h) u := by
  intro u hu
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hu
  obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp he
  apply edge_match b h _ _ _ ((ABLayout.free_injective l).ne (UniformK61.CommonSoundness.ordered_ne ab hab))
  rw [referenceMap_free,referenceMap_free]
  simpa only [frame,physical_free] using hg.free _ _ (UniformK61.CommonSoundness.ordered_ne ab hab)

theorem label61_eq (b : Blocks c l t) (p : Fin 737)
    (hf : freeSize l=(pairTable p).shape.free)
    (hp : PricingIntegration.PairAdmission.retained p=sourceRecord b (pairTable p).shape)
    (a : Fin (pairTable p).shape.dimension) :
    label61 l p a.val=UniformK61.CommonHost.retain l
      (supportIndex b (pairTable p).shape hf p hp a) := by
  apply Fin.ext
  dsimp [label61]
  rw [CommonReference.label_supportIndex b p hf hp a]
  exact Nat.mod_eq_of_lt (UniformK61.CommonHost.retain l
    (supportIndex b (pairTable p).shape hf p hp a)).isLt

theorem word_match (b z : Blocks c l t) (h : Completion z missing) (p : Fin 737)
    (hf : freeSize l=(pairTable p).shape.free)
    (hp : PricingIntegration.PairAdmission.retained p=sourceRecord b (pairTable p).shape)
    (j : Fin (pairTable p).count)
    (hmat : ∀ a d : Fin (pairTable p).shape.dimension,a≠d →
      c ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp a))
        ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp d))=
        palette (matrix (pairTable p).shape ((pairTable p).representative j) a d)) :
    ∀ u ∈ word l p j,UniformK61.Core.UnitMatches (referenceColoring z h) u := by
  intro u hu
  have hm : u∈rawWord l p j := by
    unfold word at hu
    split_ifs at hu
    · exact List.mem_mergeSort.mp hu
    · exact hu
  obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hm
  have hn : ab.1≠ab.2 := by
    rcases List.mem_append.mp hab with h|h
    · rcases List.mem_append.mp h with h|h
      · exact product_ne _ 0 1 (by decide) ab h
      · exact product_ne _ 0 2 (by decide) ab h
    · exact product_ne _ 1 2 (by decide) ab h
  have hs := (supportIndex_injective b (pairTable p).shape hf p hp).ne hn
  change label61 l p ab.1.val≠label61 l p ab.2.val ∧ _
  rw [label61_eq b p hf hp ab.1,label61_eq b p hf hp ab.2]
  refine ⟨(UniformK61.CommonHost.retain_injective l).ne hs,?_⟩
  change c (referenceMap z h (UniformK61.CommonHost.retain l _))
    (referenceMap z h (UniformK61.CommonHost.retain l _))=_
  rw [referenceMap_support b z h p hf hp,referenceMap_support b z h p hf hp]
  exact hmat _ _ hn

theorem membershipFor_match (b : Blocks c l t) (h : Completion b missing)
    (hc : NoMonochromaticTriangle c) (ls rs : Finset Nat)
    (hl : ∀ v : Fin (leftSize l),c b.mark (b.left.vertex v)=palette 3 ↔
      v.val ∈ ls)
    (hr : ∀ v : Fin (rightSize l),c b.mark (b.right.vertex v)=palette 3 ↔
      v.val ∈ rs)
    (u : UniformK61.Core.PhysicalUnit) (hu : u ∈ membershipFor l ls rs) (hs : Retained l missing u) :
    UniformK61.Core.UnitMatches (referenceColoring b h) u := by
  simp only [membershipFor,List.mem_append] at hu
  rcases hu with ((hu|hu)|hu)|hu
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    apply UniformK61.CommonSoundness.signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [UniformK61.CommonHost.lowVertex] at hh;have := sizes l;omega
    · change c (referenceMap b h 60) (referenceMap b h (Reference.low l i))=palette 3 ↔ _
      rw [referenceMap_mark,referenceMap_low b h i hs.2]
      exact low_membership b h _
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    apply UniformK61.CommonSoundness.signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [UniformK61.CommonHost.leftVertex] at hh;have := sizes l;unfold lowSize tailSize at hh;omega
    · change c (referenceMap b h 60) (referenceMap b h (Reference.left l i))=palette 3 ↔ _
      rw [referenceMap_mark,referenceMap_left]
      exact hl i
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    apply UniformK61.CommonSoundness.signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [UniformK61.CommonHost.rightVertex] at hh;have := sizes l;unfold lowSize tailSize at hh;omega
    · change c (referenceMap b h 60) (referenceMap b h (Reference.right l i))=palette 3 ↔ _
      rw [referenceMap_mark,referenceMap_right]
      exact hr i
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    refine ⟨?_,?_⟩
    · intro he;have hh := congrArg Fin.val he;dsimp [UniformK61.CommonHost.markedVertex] at hh;omega
    · obtain ⟨j,hj⟩ := marked_preimage l missing ⟨i.val,by omega⟩ hs.2
      change c (referenceMap b h 60)
        (referenceMap b h (Reference.marked l ⟨i.val,by omega⟩))≠palette 3
      rw [←hj,referenceMap_mark,referenceMap_marked,←h.mark_eq]
      apply neighborhood_avoids_own_color c hc
        (h.marked.mem_neighborhood (markIndex missing)) (h.marked.mem_neighborhood j)
      apply h.marked.vertex.injective.ne
      intro he
      have hv := congrArg (markedPosition missing) he
      rw [markedPosition_mark,hj] at hv
      have hvi : (15 : Nat)=i.val := congrArg Fin.val hv
      have := i.isLt
      omega

theorem membership_match (b : Blocks c l t) (h : Completion b missing)
    (hc : NoMonochromaticTriangle c) (p : Fin 737)
    (hl : ∀ v : Fin (leftSize l),c b.mark (b.left.vertex v)=palette 3 ↔
      v.val ∈ (PricingIntegration.PairAdmission.retained p).left)
    (hr : ∀ v : Fin (rightSize l),c b.mark (b.right.vertex v)=palette 3 ↔
      v.val ∈ (PricingIntegration.PairAdmission.retained p).right)
    (u : UniformK61.Core.PhysicalUnit) (hu : u ∈ membership l p) (hs : Retained l missing u) :
    UniformK61.Core.UnitMatches (referenceColoring b h) u :=
  membershipFor_match b h hc _ _ hl hr u hu hs

/-- The exact signed restricted formula has a physical satisfying valuation.
Only the fresh actual60 base is used, and the omitted reference facts are
absent from the hypotheses. -/
theorem common_restriction_satisfiable (b z : Blocks c l t) (h : Completion z missing)
    (hc : NoMonochromaticTriangle c) (p : Fin 737)
    (hf : freeSize l=(pairTable p).shape.free)
    (hp : PricingIntegration.PairAdmission.retained p=sourceRecord b (pairTable p).shape)
    (j : Fin (pairTable p).count) (hg : CommonBlocks.Geometry t (frame z))
    (hmat : ∀ a d : Fin (pairTable p).shape.dimension,a≠d →
      c ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp a))
        ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp d))=
        palette (matrix (pairTable p).shape ((pairTable p).representative j) a d))
    (hl : ∀ v : Fin (leftSize l),c z.mark (z.left.vertex v)=palette 3 ↔
      v.val ∈ (PricingIntegration.PairAdmission.retained p).left)
    (hr : ∀ v : Fin (rightSize l),c z.mark (z.right.vertex v)=palette 3 ↔
      v.val ∈ (PricingIntegration.PairAdmission.retained p).right) :
    ∃ w : DenseCounter.Valuation,DenseCounter.FormulaSat w
      (UnitRestriction.formula (omission l missing)
        (ReferenceSource.units (UniformK61.CommonFormula.units l t p j))) := by
  apply restriction_satisfiable (referenceColoring z h) (omission l missing) _
    (reference_restrict_good z h hc)
  intro u hu hs
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
  change UniformK61.Core.UnitMatches (referenceColoring z h) v
  simp only [UniformK61.CommonFormula.units,List.mem_append] at hv
  rcases hv with (((hv|hv)|hv)|hv)|hv
  · exact spokes_match z h v hv hs
  · exact templates_match z h v hv hs
  · exact free_match z h hg v hv
  · exact word_match b z h p hf hp j hmat v hv
  · exact membership_match z h hc p hl hr v hv hs

#print axioms common_restriction_satisfiable
end UniformK60.CommonSoundness
