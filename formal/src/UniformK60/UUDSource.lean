import UniformK60.UUReferenceD
import UniformK60.UUD

set_option autoImplicit false
namespace UniformK60.UUDSource
open Ramsey61 Finset UniformK60.Physical
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonReference
open UniformK60.ClassificationSupports UniformK60.UUPhysicalCover UniformK60.UUCoordinates
open UniformK60.UUReferenceD UniformK60.UUSourceFacts
open CompletionC.NativeMatrices UniformK60.NativeCatalogue
open UniformK61.UUSupportData UniformK61.UUPureCoordinates

private theorem nat_mem_set {n : Nat} (S : Finset (Fin n)) (v : Fin n) :
    v.val∈S.image Fin.val ↔ v∈S := by
  constructor
  · rintro h
    obtain ⟨a,ha,he⟩ := mem_image.mp h
    exact (Fin.ext he : a=v) ▸ ha
  · intro h
    exact mem_image.mpr ⟨v,h,rfl⟩

theorem source_from_catalogue {c : Host} (q : Bool) (p : Pair)
    (b : Blocks c (layout p) ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c)
    (hl : support (side:=false) b.left b.mark=leftSet p)
    (hr : support (side:=true) b.right b.mark=rightSet p)
    (perm : Equiv.Perm (Fin (shape p).free)) (i : Fin 600)
    (hmat : ∀ a d : Fin (shape p).dimension,a≠d →
      c (reorderedVertex (shape p) (supportFrame q p b hl hr) perm a)
        (reorderedVertex (shape p) (supportFrame q p b hl hr) perm d)=
      palette (matrix (shape p) (candidate (shape p) i) a d))
    (h : Completion (reorderFree b (freePermutation p perm)) none) :
    SourceFacts q p i (completed (reorderFree b (freePermutation p perm)) h) := by
  let z := reorderFree b (freePermutation p perm)
  have hleft : ∀ v : Fin 15,c z.mark (z.left.vertex v)=palette 3 ↔ v.val∈leftNats p := by
    intro v
    rw [leftNats,nat_mem_set,←hl]
    change (c b.mark (b.left.vertex v)=palette 3) ↔ v∈univ.filter (fun x => c b.mark (b.left.vertex x)=palette 3)
    constructor
    · intro he;exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,he⟩
    · intro he;exact (Finset.mem_filter.mp he).2
  have hright : ∀ v : Fin 15,c z.mark (z.right.vertex v)=palette 3 ↔ v.val∈rightNats p := by
    intro v
    rw [rightNats,nat_mem_set,←hr]
    change (c b.mark (b.right.vertex v)=palette 3) ↔ v∈univ.filter (fun x => c b.mark (b.right.vertex x)=palette 3)
    constructor
    · intro he;exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,he⟩
    · intro he;exact (Finset.mem_filter.mp he).2
  refine { toStaticHost := UUReferenceD.static z h, membership := ?_, matrix := ?_ }
  · intro v hv
    by_cases hzero : v=0
    · subst v
      have hs := UUReferenceD.spokes z h 60 (by decide)
      simpa [UniformK61.UUSourceDefs.member,UniformK61.UUSourceDefs.rootColor,
        UniformK61.Core.palette,CEncodingCore.palette,Physical.palette] using hs
    by_cases h14 : v=14
    · subst v
      have hf : (shape p).free≤5 := by cases shape p <;> decide
      simp [completed,ReferenceExtension.extend,UniformK61.UUSourceDefs.member,
        show ¬14≤(shape p).free by omega,Physical.palette,
        UniformK61.Core.palette,CEncodingCore.palette]
    · obtain ⟨u,hu,hpos,hum,huv,huq⟩ := matching_unit p v hzero hv
      have hs : CommonSoundness.Retained (layout p) none u := by
        constructor
        · change u.u ≠ (14:Fin 61);rw [hum];decide
        · change u.v ≠ (14:Fin 61);rw [huv];exact h14
      have hf := CommonSoundness.membershipFor_match z h hc (leftNats p) (rightNats p)
        hleft hright u hu hs
      have hm := matched_iff (referenceColoring z h) u hf
      rw [hpos,hum,huv,huq] at hm
      rw [UUReferenceD.agrees z h v 60 h14 (by decide),(referenceColoring z h).color_symm v 60]
      exact hm
  · intro a d had
    rw [UUReferenceD.agrees z h _ _ (matrix_vertex_ne_fourteen p a) (matrix_vertex_ne_fourteen p d)]
    change c (referenceMap z h (UniformK61.UUSourceDefs.matrixVertex p a))
      (referenceMap z h (UniformK61.UUSourceDefs.matrixVertex p d))=_
    rw [UUCoordinates.matrix_vertex q p b hl hr perm h a,
      UUCoordinates.matrix_vertex q p b hl hr perm h d]
    exact hmat a d had

/-- The exact1358 D/U/U formulas follow from actual support geometry and
the actual marked16 completion. Only the common placement is a hypothesis. -/
theorem exact_D_from_catalogue {c : Host} (q : Bool) (p : Pair)
    (b : Blocks c (layout p) ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c)
    (hl : support (side:=false) b.left b.mark=leftSet p)
    (hr : support (side:=true) b.right b.mark=rightSet p)
    (perm : Equiv.Perm (Fin (shape p).free)) (i : Fin 600)
    (hmat : ∀ a d : Fin (shape p).dimension,a≠d →
      c (reorderedVertex (shape p) (supportFrame q p b hl hr) perm a)
        (reorderedVertex (shape p) (supportFrame q p b hl hr) perm d)=
      palette (matrix (shape p) (candidate (shape p) i) a d))
    (h : Completion (reorderFree b (freePermutation p perm)) none) :
    ∃ j : UniformK61.MarkedUU.Leaf,∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (ABDFormula.formula (.inr (q,j))) :=
  UUD.reference_to_exact_D (source_from_catalogue q p b hc hl hr perm i hmat h)
    (UUReferenceD.restriction_good _ h hc)

#print axioms exact_D_from_catalogue
end UniformK60.UUDSource
