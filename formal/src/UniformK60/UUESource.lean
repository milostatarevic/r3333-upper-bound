import UniformK60.UUReferenceE

set_option autoImplicit false
namespace UniformK60.UUESource
open Ramsey61 Finset UniformK60.Physical
open UniformK60.CommonBlocks UniformK60.CommonHost UniformK60.CommonReference
open UniformK60.ClassificationSupports UniformK60.UUPhysicalCover UniformK60.UUCoordinates
open UniformK60.UUReferenceE UniformK60.UUSourceFacts
open CompletionC.NativeMatrices UniformK60.NativeCatalogue
open UniformK61.UUSupportData UniformK61.UUPureCoordinates

private theorem nat_mem_set {n : Nat} (S : Finset (Fin n)) (v : Fin n) :
    v.val∈S.image Fin.val ↔ v∈S := by
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := mem_image.mp h
    exact (Fin.ext he : a=v) ▸ ha
  · intro h
    exact mem_image.mpr ⟨v,h,rfl⟩

theorem matrix_vertex_small (p : Pair) (a : Fin (shape p).dimension) :
    (UniformK61.UUSourceDefs.matrixVertex p a).val≤44 := by
  have hf : (shape p).free≤5 := by cases shape p <;> decide
  unfold UniformK61.UUSourceDefs.matrixVertex
  split_ifs with h0 h1
  · change a.val+1≤44
    omega
  · dsimp [UniformK61.UUSourceDefs.leftVertex]
    omega
  · dsimp [UniformK61.UUSourceDefs.rightVertex]
    omega

theorem source_from_catalogue {c : Host} (q : Bool) (p : Pair)
    (b : Blocks c (layout p) ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c)
    (hl : support (side:=false) b.left b.mark=leftSet p)
    (hr : support (side:=true) b.right b.mark=rightSet p)
    (perm : Equiv.Perm (Fin (shape p).free)) (i : Fin 600)
    (hmat : ∀ a d : Fin (shape p).dimension,a≠d →
      c (reorderedVertex (shape p) (supportFrame q p b hl hr) perm a)
        (reorderedVertex (shape p) (supportFrame q p b hl hr) perm d)=
      palette (matrix (shape p) (candidate (shape p) i) a d))
    (r : Fin 15) (h : Completion (reorderFree b (freePermutation p perm)) (some r)) :
    SourceFacts q p i (completed (reorderFree b (freePermutation p perm)) r h) := by
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
  have hstatic := UUReferenceE.static z r h
  refine { toStaticHost := hstatic, membership := ?_, matrix := ?_ }
  · intro v hv
    by_cases hzero : v=0
    · subst v
      have hs := UUReferenceE.spokes z r h 60 (by decide)
      simpa [UniformK61.UUSourceDefs.member,UniformK61.UUSourceDefs.rootColor,
        UniformK61.Core.palette,CEncodingCore.palette,Physical.palette] using hs
    by_cases hd : v=(UUE.omitted r).castSucc
    · subst v
      have hm := UniformK61.UUResidualTransport.member_high p (UUE.omitted r).castSucc (by
        change 45≤45+r.val;omega)
      rw [hm]
      simp only [Bool.false_eq_true,iff_false]
      have hn : r.castSucc≠(15:Fin 16) := by
        intro he
        have hh := congrArg Fin.val he
        change r.val=15 at hh
        omega
      have ht := hstatic.marked r.castSucc 15 hn
      change completed z r h (UniformK61.UUBridgeData.qVertex r.castSucc)
        (UniformK61.UUBridgeData.qVertex 15)≠UniformK61.Core.palette 3
      rw [ht]
      exact fun he => PricingABD.ABGeometry.foreign_ne 3 _ (CEncodingCore.palette_injective he)
    · obtain ⟨u,hu,hpos,hum,huv,huq⟩ := matching_unit p v hzero hv
      have hs : CommonSoundness.Retained (layout p) (some r) u := by
        constructor
        · change u.u≠(UUE.omitted r).castSucc
          rw [hum];exact CommonCoordinates.mark_survives (layout p) (some r)
        · change u.v≠(UUE.omitted r).castSucc
          rw [huv];exact hd
      have hf := CommonSoundness.membershipFor_match z h hc (leftNats p) (rightNats p)
        hleft hright u hu hs
      have hm := matched_iff (referenceColoring z h) u hf
      rw [hpos,hum,huv,huq] at hm
      rw [UUReferenceE.agrees z r h v 60 hd (CommonCoordinates.mark_survives (layout p) (some r)),
        (referenceColoring z h).color_symm v 60]
      exact hm
  · intro a d had
    rw [UUReferenceE.agrees z r h _ _ (small_ne r _ (matrix_vertex_small p a))
      (small_ne r _ (matrix_vertex_small p d))]
    change c (referenceMap z h (UniformK61.UUSourceDefs.matrixVertex p a))
      (referenceMap z h (UniformK61.UUSourceDefs.matrixVertex p d))=_
    rw [UUCoordinates.matrix_vertex q p b hl hr perm h a,
      UUCoordinates.matrix_vertex q p b hl hr perm h d]
    exact hmat a d had

theorem exact_E_from_catalogue {c : Host} (q : Bool) (p : Pair)
    (b : Blocks c (layout p) ⟨false,false,q⟩) (hc : NoMonochromaticTriangle c)
    (hl : support (side:=false) b.left b.mark=leftSet p)
    (hr : support (side:=true) b.right b.mark=rightSet p)
    (perm : Equiv.Perm (Fin (shape p).free)) (i : Fin 600)
    (hmat : ∀ a d : Fin (shape p).dimension,a≠d →
      c (reorderedVertex (shape p) (supportFrame q p b hl hr) perm a)
        (reorderedVertex (shape p) (supportFrame q p b hl hr) perm d)=
      palette (matrix (shape p) (candidate (shape p) i) a d))
    (r : Fin 15) (h : Completion (reorderFree b (freePermutation p perm)) (some r)) :
    ∃ k : EFormula.Case,∃ v : DenseCounter.Valuation,DenseCounter.FormulaSat v (EFormula.formula k) :=
  UUE.reference_to_exact_E (source_from_catalogue q p b hc hl hr perm i hmat r h) r
    (UUReferenceE.restriction_good _ r h hc)

#print axioms exact_E_from_catalogue
end UniformK60.UUESource
