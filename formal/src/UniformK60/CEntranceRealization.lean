import UniformK60.CEntranceCanonical

/-! Turn the closed physical common cover into the source witness consumed
by the exact finite transport. Every signed fact is about an actual edge. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.CEntranceRealization
open Ramsey61 Finset UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CommonBlocks UniformK60.CommonPairAdmission
open UniformK60.CEntranceSource UniformK60.CEntranceLayout UniformK60.CEntranceCanonical
open UniformK60.ClassificationGeometry UniformK60.PhysicalHelpers
open UniformK60.NativeSupportIndex
open PricingIntegration.PairAdmission CompletionC.NativeMatrices

private theorem native_palette (own : Color) (q : Fin 3) :
    (foreignEquiv own q).val=palette (PricingABD.ABGeometry.foreign own q) := by
  fin_cases own <;> fin_cases q <;> rfl

theorem source_types {c : Host} {mode : Mode} {five : Bool}
    {t : PricingABD.ABLayout.Types} (b : Blocks c (layout mode five) t)
    (p : Fin 737) (hp : retained p=sourceRecord b (pairTable p).shape) :
    leftType p=t.left ∧ rightType p=t.right ∧ Eligible mode p := by
  have hl := congrArg Record.leftKind hp
  have hr := congrArg Record.rightKind hp
  have hf := congrArg Record.family hp
  refine ⟨?_,?_,?_⟩
  · unfold leftType
    rw [hl]
    change decide (UniformK60.CommonSupportNormalization.kindCode
      (PricingABD.ABLayout.leftLarge (layout mode five)) t.left % 2=1)=t.left
    cases PricingABD.ABLayout.leftLarge (layout mode five) <;> cases t.left <;> rfl
  · unfold rightType
    rw [hr]
    change decide (UniformK60.CommonSupportNormalization.kindCode
      (PricingABD.ABLayout.rightLarge (layout mode five)) t.right % 2=1)=t.right
    cases PricingABD.ABLayout.rightLarge (layout mode five) <;> cases t.right <;> rfl
  · unfold Eligible
    rw [hf]
    fin_cases mode <;> rfl

private theorem left_model (mode : Mode) (five t : Bool) (a b : Fin (leftSize mode)) :
    PricingABD.ABGeometry.model (PricingABD.ABLayout.leftLarge (layout mode five)) t
      ((finCongr (left_size mode five).symm) a) ((finCongr (left_size mode five).symm) b)=
      leftTemplate mode t a b := by
  fin_cases mode <;> cases five <;> rfl

private theorem right_model (mode : Mode) (five t : Bool) (a b : Fin 16) :
    PricingABD.ABGeometry.model (PricingABD.ABLayout.rightLarge (layout mode five)) t
      ((finCongr (right_size mode five).symm) a) ((finCongr (right_size mode five).symm) b)=
      R4333.k16Template t a b := by
  fin_cases mode <;> cases five <;> rfl

private theorem free_support_after_placement {c : Host} {mode : Mode} {five : Bool}
    {t : PricingABD.ABLayout.Types} (z : Blocks c (layout mode five) t)
    (e : Vertex ≃ Vertex)
    (he : ∀ v,rootCell c z.root (Equiv.refl _) (e v)=cell mode v)
    (hef : ∀ i,e (freeEmbedding (low_free_bound mode five) i)=z.free i)
    (hem : e 59=z.mark) (v : Vertex) (hv : v≠0) (hcell : v.val≤lowSize mode) :
    relabel c e (Equiv.refl _) v 59=palette 3 ↔
      v.val≤PricingABD.ABLayout.freeSize (layout mode five) := by
  have hmem : e v∈colorNeighborhood c (palette 0) z.root := by
    apply (rootCell_some c z.root (e v) (Equiv.refl _) (palette 0)).mp
    rw [he]
    simp [cell,hv,rootColor,hcell]
  have hne : e v≠z.mark := by
    intro h
    exact False.elim (by
      have hval : v.val=59 := congrArg Fin.val (e.injective (h.trans hem.symm))
      have hh : lowSize mode≤14 := by fin_cases mode <;> decide
      omega)
  have hs : c (e v) z.mark=palette 3 ↔ ∃ i,z.free i=e v := by
    constructor
    · intro hc
      apply (z.free_exact (e v)).mp
      exact mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr
        ⟨hne,(c.color_symm z.mark (e v)).trans hc⟩,hmem⟩
    · rintro ⟨i,hi⟩
      rw [←hi,c.color_symm]
      exact z.free_own i
  change c (e v) (e 59)=palette 3 ↔ _
  rw [hem,hs]
  constructor
  · rintro ⟨i,hi⟩
    have heq : freeEmbedding (low_free_bound mode five) i=v :=
      e.injective ((hef i).trans hi)
    have hval : 1+i.val=v.val := congrArg Fin.val heq
    have hi := i.isLt
    omega
  · intro hsize
    have hpos : 0<v.val := by
      have : v.val≠0 := fun h => hv (Fin.ext h)
      omega
    let i : Fin (PricingABD.ABLayout.freeSize (layout mode five)) := ⟨v.val-1,by omega⟩
    refine ⟨i,(hef i).symm.trans ?_⟩
    apply congrArg e
    apply Fin.ext
    change 1+(v.val-1)=v.val
    omega

/-- Complete simultaneous placement and source semantics for any native
A/B entrance word; no constraints on the marked root cell are introduced. -/
theorem realize {c : Host} {mode : Mode} {five : Bool}
    {t : PricingABD.ABLayout.Types} (b z : Blocks c (layout mode five) t)
    (hc : NoMonochromaticTriangle c)
    (hd : ∀ q : Color,colorDegree c (palette q) z.root=CEntranceLayout.shape mode q)
    (p : Fin 737) (hf : PricingABD.ABLayout.freeSize (layout mode five)=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape)
    (j : Fin (pairTable p).count)
    (hmat : ∀ a v : Fin (pairTable p).shape.dimension,a≠v →
      c ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp a))
        ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp v))=
        palette (matrix (pairTable p).shape ((pairTable p).representative j) a v))
    (hl : ∀ i : Fin (PricingABD.ABLayout.leftSize (layout mode five)),
      c z.mark (z.left.vertex i)=palette 3 ↔ i.val∈(retained p).left)
    (hr : ∀ i : Fin (PricingABD.ABLayout.rightSize (layout mode five)),
      c z.mark (z.right.vertex i)=palette 3 ↔ i.val∈(retained p).right) :
    ∃ d : Host,SourceWitness mode p j d := by
  obtain ⟨htl,htr,_⟩ := source_types b p hp
  obtain ⟨e,he0,he,hef,hel,her,hem⟩ := CEntrancePlacement.place (low_free_bound mode five)
    z.root z.mark z.free (leftMap z) (rightMap z) hd z.free_mem
      (fun i => z.left.mem_neighborhood _) (fun i => z.right.mem_neighborhood _) z.mark_mem
  let d := relabel c e (Equiv.refl _)
  have good : NoMonochromaticTriangle d := relabel_noMono c hc _ _
  have spokes : ∀ v : Vertex,v≠0 → d 0 v=palette (rootColor mode v) := by
    intro v hv
    exact relabel_root_spoke c z.root (Equiv.refl _) (cell mode) e he0 he v _
      (by simp [cell,hv])
  refine ⟨d,good,spokes,?_,?_,?_,?_⟩
  · intro a v hav
    change c (e (leftVertex mode a)) (e (leftVertex mode v))=_
    rw [hel,hel]
    change c (z.left.vertex _) (z.left.vertex _)=_
    erw [z.left.map_color _ _ ((finCongr (left_size mode five).symm).injective.ne hav),
      z.left_palette,native_palette,left_model,htl]
  · intro a v hav
    change c (e (rightVertex mode a)) (e (rightVertex mode v))=_
    rw [her,her]
    change c (z.right.vertex _) (z.right.vertex _)=_
    erw [z.right.map_color _ _ ((finCongr (right_size mode five).symm).injective.ne hav),
      z.right_palette,native_palette,right_model,htr]
  · apply CEntranceMembership.membership_from_cells good mode p spokes
    · intro v hv hcell
      rw [←hf]
      exact free_support_after_placement z e he hef hem v hv hcell
    · intro i
      change c (e (leftVertex mode i)) (e 59)=palette 3 ↔ _
      rw [hel,hem,c.color_symm]
      exact hl _
    · intro i
      change c (e (rightVertex mode i)) (e 59)=palette 3 ↔ _
      rw [her,hem,c.color_symm]
      exact hr _
  · intro a v hav
    change c (e (matrixVertex mode p a)) (e (matrixVertex mode p v))=_
    rw [placed_matrix b z p hf hp e hef hel her,placed_matrix b z p hf hp e hef hel her]
    exact hmat a v hav

#print axioms realize
end UniformK60.CEntranceRealization
