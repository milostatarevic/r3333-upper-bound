import UniformK61.UUPureCoordinates
import UniformK61.UUFiniteCover
import CompletionC.CommonShapes
import CompletionC.NativeCatalogue

set_option autoImplicit false
namespace UniformK61.UUPhysicalCover
open Ramsey61 Ramsey61.CEncodingCore Finset
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open CompletionC.CommonBlocks CompletionC.CommonSupportNormalization CompletionC.CommonShapes
open CompletionC.NativeMatrices CompletionC.NativeCatalogue
open PricingIntegration.PhysicalForeignSupport PricingIntegration.PairAdmission
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
      support (side:=false) z.left (z.marked.vertex 15)=leftSet p ∧
      support (side:=true) z.right (z.marked.vertex 15)=rightSet p := by
  obtain ⟨sl,sr,z,_,_,_,hn⟩ := normalize_foreign b hc
  obtain ⟨s,hf,hl,hr⟩ := normalized_shape z hc sl sr hn
  have hleft : support (side:=false) z.left (z.marked.vertex 15)∈supports s.left := by
    apply (reps_iff _ sl s.left hl).mp
    exact hn.2.2.1
  have hright : support (side:=true) z.right (z.marked.vertex 15)∈supports s.right := by
    apply (reps_iff _ sr s.right hr).mp
    exact hn.2.2.2
  obtain ⟨p,hp,hpl,hpr⟩ := pairs_cover s _ hleft _ hright
  have hfive : five=UUSupportData.five p := by
    unfold UUSupportData.five
    rw [hp]
    cases five <;> cases s <;> simp_all [freeSize,Shape.free]
  subst five
  exact ⟨p,z,hpl.symm,hpr.symm⟩

noncomputable def supportFrame (q : Bool) (p : Pair)
    (b : Blocks c (layout p) ⟨false,false,q⟩)
    (hl : support (side:=false) b.left (b.marked.vertex 15)=leftSet p)
    (hr : support (side:=true) b.right (b.marked.vertex 15)=rightSet p) :
    PricingC.ThreeSupportFrame.Frame c (shape p).free (shape p).left (shape p).right where
  root := b.root
  mark := b.marked.vertex 15
  free := (finCongr (layout_free p).symm).toEmbedding.trans b.free
  left := (leftEmbedding p).trans b.left.vertex
  right := (rightEmbedding p).trans b.right.vertex
  mark_mem := b.marked.mem_neighborhood 15
  free_mem i := b.free_mem _
  left_mem i := b.left.mem_neighborhood _
  right_mem i := b.right.mem_neighborhood _
  marked_free i := b.free_own _
  marked_left i := by
    have h : leftOrder p i∈support (side:=false) b.left (b.marked.vertex 15) := by
      rw [hl];exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    exact (mem_filter.mp h).2
  marked_right i := by
    have h : rightOrder p i∈support (side:=true) b.right (b.marked.vertex 15) := by
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

/-- Only the complete free support is reordered, inside the same host. -/
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
        refine ⟨perm.symm i,?_⟩
        exact congrArg b.free (perm.apply_symm_apply i)
      · rintro ⟨i,rfl⟩
        exact ⟨perm i,rfl⟩ }

noncomputable def freePermutation (p : Pair) (perm : Equiv.Perm (Fin (shape p).free)) :
    Equiv.Perm (Fin (freeSize (layout p))) :=
  (finCongr (layout_free p)).trans (perm.trans (finCongr (layout_free p).symm))

theorem matrix_vertex (q : Bool) (p : Pair) (b : Blocks c (layout p) ⟨false,false,q⟩)
    (hl : support (side:=false) b.left (b.marked.vertex 15)=leftSet p)
    (hr : support (side:=true) b.right (b.marked.vertex 15)=rightSet p)
    (perm : Equiv.Perm (Fin (shape p).free)) (a : Fin (shape p).dimension) :
    CommonHost.fullMap (reorderFree b (freePermutation p perm)) (UUSourceDefs.matrixVertex p a)=
      reorderedVertex (shape p) (supportFrame q p b hl hr) perm a := by
  rw [reorderedVertex_formula]
  unfold UUSourceDefs.matrixVertex
  split_ifs with h0 h1
  · have hf : a.val<freeSize (layout p) := by rw [layout_free];exact h0
    have he : (⟨a.val+1,by
          have h : (shape p).free≤5 := by cases shape p <;> decide
          omega⟩ : Vertex)=
        CommonHost.lowVertex (layout p) ⟨a.val,by have := sizes (layout p);omega⟩ := by
      apply Fin.ext;dsimp [CommonHost.lowVertex];omega
    rw [he,CommonHost.fullMap_low]
    simp only [CommonHost.low,hf,dif_pos]
    rfl
  · change CommonHost.fullMap (reorderFree b (freePermutation p perm))
        (CommonHost.leftVertex (layout p) (leftOrder p ⟨a.val-(shape p).free,by omega⟩))=_
    rw [CommonHost.fullMap_left]
    rfl
  · change CommonHost.fullMap (reorderFree b (freePermutation p perm))
        (CommonHost.rightVertex (layout p) (rightOrder p
          ⟨a.val-(shape p).free-(shape p).left,by have h:=Shape.dimension_sum (shape p);have ha:=a.isLt;omega⟩))=_
    rw [CommonHost.fullMap_right]
    rfl

private theorem nat_mem_set {n : Nat} (S : Finset (Fin n)) (v : Fin n) :
    v.val∈S.image Fin.val ↔v∈S := by
  constructor
  · rintro h
    obtain ⟨a,ha,he⟩ := mem_image.mp h
    exact (Fin.ext he : a=v) ▸ ha
  · intro h
    exact mem_image.mpr ⟨v,h,rfl⟩

/-- A normalized support pair and a catalogue word give facts in a complete
61-vertex coloring. Only the free support is reordered by the catalogue. -/
theorem source_from_catalogue (q : Bool) (p : Pair)
    (b : Blocks c (layout p) ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c)
    (hl : support (side:=false) b.left (b.marked.vertex 15)=leftSet p)
    (hr : support (side:=true) b.right (b.marked.vertex 15)=rightSet p)
    (perm : Equiv.Perm (Fin (shape p).free)) (i : Fin 600)
    (hmat : ∀a d : Fin (shape p).dimension,a≠d→
      c (reorderedVertex (shape p) (supportFrame q p b hl hr) perm a)
        (reorderedVertex (shape p) (supportFrame q p b hl hr) perm d)=
      palette (matrix (shape p) (candidate (shape p) i) a d)) :
    UUSourceDefs.SourceWitness q p i
      (CommonHost.coloring (reorderFree b (freePermutation p perm))) := by
  let z := reorderFree b (freePermutation p perm)
  have hsp : ∀v : Vertex,v≠0→CommonHost.coloring z 0 v=palette (UUSourceDefs.rootColor v) := by
    intro v hv
    obtain ⟨u,hu,hpos,hur,huv,huq⟩ := matching_spoke (five p) v hv
    have hm := matched_iff (CommonHost.coloring z) u (CommonSoundness.spokes_match z u hu)
    simpa only [hur,huv,huq] using hm.mpr hpos
  have hleft : ∀v : Fin 15,c (z.marked.vertex 15) (z.left.vertex v)=palette 3 ↔ v.val∈leftNats p := by
    intro v
    rw [leftNats,nat_mem_set,←hl]
    change _ ↔v∈univ.filter (fun x => c (b.marked.vertex 15) (b.left.vertex x)=palette 3)
    constructor
    · intro h;exact mem_filter.mpr ⟨mem_univ v,h⟩
    · intro h;exact (mem_filter.mp h).2
  have hright : ∀v : Fin 15,c (z.marked.vertex 15) (z.right.vertex v)=palette 3 ↔ v.val∈rightNats p := by
    intro v
    rw [rightNats,nat_mem_set,←hr]
    change _ ↔v∈univ.filter (fun x => c (b.marked.vertex 15) (b.right.vertex x)=palette 3)
    constructor
    · intro h;exact mem_filter.mpr ⟨mem_univ v,h⟩
    · intro h;exact (mem_filter.mp h).2
  refine ⟨CommonHost.coloring_good z hc,hsp,?_,?_,?_,?_,?_⟩
  · intro a d had
    change c (CommonHost.fullMap z (CommonHost.leftVertex (layout p) a))
      (CommonHost.fullMap z (CommonHost.leftVertex (layout p) d))=_
    rw [CommonHost.fullMap_left,CommonHost.fullMap_left]
    erw [z.left.map_color a d had,z.left_palette]
    change palette (PricingIntegration.BActualFrame.foreign 1 (R4333.k15Template false a d))=
      palette (foreign 1 (R4333.k15Template false a d))
    generalize R4333.k15Template false a d=col
    fin_cases col <;> rfl
  · intro a d had
    change c (CommonHost.fullMap z (CommonHost.rightVertex (layout p) a))
      (CommonHost.fullMap z (CommonHost.rightVertex (layout p) d))=_
    rw [CommonHost.fullMap_right,CommonHost.fullMap_right]
    erw [z.right.map_color a d had,z.right_palette]
    change palette (PricingIntegration.BActualFrame.foreign 2 (R4333.k15Template false a d))=
      palette (foreign 2 (R4333.k15Template false a d))
    generalize R4333.k15Template false a d=col
    fin_cases col <;> rfl
  · intro a d had
    change c (CommonHost.fullMap z (CommonHost.markedVertex (layout p) a))
      (CommonHost.fullMap z (CommonHost.markedVertex (layout p) d))=_
    rw [CommonHost.fullMap_marked,CommonHost.fullMap_marked]
    simpa only [frame,physical_marked] using marked_edges z a d had
  · intro v hv
    by_cases hzero : v=0
    · subst v
      have h := hsp 60 (by decide)
      simpa [UUSourceDefs.member,UUSourceDefs.rootColor,Core.palette,z] using h
    · obtain ⟨u,hu,hpos,hum,huv,huq⟩ := matching_unit p v hzero hv
      have hs := CommonSoundness.membershipFor_match z hc (leftNats p) (rightNats p) hleft hright u hu
      have hm := matched_iff (CommonHost.coloring z) u hs
      rw [hpos,hum,huv,huq] at hm
      change CommonHost.coloring z v 60=Core.palette 3 ↔_
      rw [(CommonHost.coloring z).color_symm v 60]
      exact hm
  · intro a d had
    change c (CommonHost.fullMap z (UUSourceDefs.matrixVertex p a))
      (CommonHost.fullMap z (UUSourceDefs.matrixVertex p d))=_
    rw [matrix_vertex q p b hl hr perm a,matrix_vertex q p b hl hr perm d]
    exact hmat a d had

/-- Full-host marked-neighborhood extraction for both D/U/U families. -/
theorem actual_UU_source {c : Host} {five : Bool} (q : Bool)
    (b : Blocks c ⟨.D,five⟩ ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c) :
    ∃p : Pair,∃i : Fin 600,∃d : Host,UUSourceDefs.SourceWitness q p i d := by
  obtain ⟨p,z,hl,hr⟩ := normalized_pair q b hc
  obtain ⟨perm,i,hmat⟩ := actual_catalogue (shape p) (supportFrame q p z hl hr) hc
  exact ⟨p,i,_,source_from_catalogue q p z hc hl hr perm i hmat⟩

/-- Every actual U/U D host reaches one of the 679 retained physical cases.
The finite bridge changes all 61 vertices by one permutation and uses one
consistent global palette action. -/
theorem actual_UU_uniform {c : Host} {five : Bool} (q : Bool)
    (b : Blocks c ⟨.D,five⟩ ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c) :
    ∃j : MarkedUU.Leaf,∃w : Ramsey61.DenseCounter.Valuation,
      Ramsey61.DenseCounter.FormulaSat w (MarkedUU.formula q j) := by
  obtain ⟨p,i,d,hs⟩ := actual_UU_source q b hc
  exact UUFiniteCover.finite_bridge_sound hs

#print axioms actual_UU_uniform
#print axioms normalized_pair
#print axioms supportFrame
#print axioms actual_UU_source
end UniformK61.UUPhysicalCover
