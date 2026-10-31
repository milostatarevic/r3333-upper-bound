import UniformK60.BalancedHostBracePlacement

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.BalancedHostBraceMembership
open Ramsey61 Finset UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationGeometry
open UniformK60.BalancedHostBraceGeometry UniformK60.BalancedHostBracePlacement
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite
open UniformK60.BalancedEncodingBraces

/-- The actual marked neighborhood is exactly the root plus its three
attaching supports; this proves all unselected membership literals negative. -/
theorem neighborhood_union (c : Host) (hc : NoMonochromaticTriangle c) (root mark : Vertex)
    (hm : mark∈colorNeighborhood c (palette 3) root) :
    colorNeighborhood c (palette 3) mark=
      insert root (support c root mark 0 ∪ support c root mark 1 ∪ support c root mark 2) := by
  have hm' := (mem_colorNeighborhood _ _ _ _).mp hm
  have hroot : root∈colorNeighborhood c (palette 3) mark :=
    (mem_colorNeighborhood _ _ _ _).mpr ⟨hm'.1.symm,(c.color_symm mark root).trans hm'.2⟩
  ext v
  constructor
  · intro hv
    by_cases hr : v=root
    · simp [hr]
    have h3 : c root v≠palette 3 := neighborhood_avoids_own_color c hc hroot hv (Ne.symm hr)
    obtain ⟨q,hq⟩ := palette_surjective (c root v)
    have hvq : v∈colorNeighborhood c (palette q) root := (mem_colorNeighborhood _ _ _ _).mpr ⟨hr,hq.symm⟩
    have hs : v∈support c root mark q := mem_inter.mpr ⟨hv,hvq⟩
    fin_cases q
    · exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ hs))
    · exact mem_insert_of_mem (mem_union_left _ (mem_union_right _ hs))
    · exact mem_insert_of_mem (mem_union_right _ hs)
    · exact False.elim (h3 hq.symm)
  · intro hv
    rcases mem_insert.mp hv with rfl|hv
    · exact hroot
    rcases mem_union.mp hv with hv|hv
    · rcases mem_union.mp hv with hv|hv <;> exact (mem_inter.mp hv).1
    · exact (mem_inter.mp hv).1

def rowFreeSizeLe (r : Row) : (rowShape r).free≤5 := by
  have h : ∀ s : CompletionC.NativeMatrices.Shape,s.free≤5 := by decide
  exact h (rowShape r)

def freeSet (r : Row) : Finset Vertex :=
  univ.image (freeVertex (n:=(rowShape r).free) (rowFreeSizeLe r))
def fakeSet : Finset Vertex := univ.image fakeVertex

def rowRealSizeLe (r : Row) : (rowShape r).right≤5 := by
  have h:=(row_dimensions r).2.2
  omega

def realSet (r : Row) : Finset Vertex := univ.image fun j : Fin (rowShape r).right =>
  realVertex (rowRealSupport r (Fin.castLE (rowRealSizeLe r) j))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem brace_set : ∀ r v,rawBrace r v=true ↔
    v∈insert 0 (freeSet r ∪ fakeSet ∪ realSet r) := by decide +kernel

theorem image_pullback {A : Type*} [Fintype A] (e : Vertex≃Vertex)
    (s t : A→Vertex) (h : ∀ a,e (s a)=t a) (v : Vertex) :
    e v∈univ.image t ↔ v∈univ.image s := by
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,e.injective ((h a).trans ha)⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a,(h a).symm⟩

/-- Signed raw membership follows from the one physical placement and the
three complete support images, without fixing any low-complement edges. -/
theorem membership_after_placement {c : Host} (hc : NoMonochromaticTriangle c)
    (root mark : Vertex) (hm : mark∈colorNeighborhood c (palette 3) root)
    (r : Row) (e : Vertex≃Vertex) (he0 : e 0=root) (hem : e 59=mark)
    (hfree : ∀ v,e v∈support c root mark 0 ↔ v∈freeSet r)
    (hfake : ∀ v,e v∈support c root mark 1 ↔ v∈fakeSet)
    (hreal : ∀ v,e v∈support c root mark 2 ↔ v∈realSet r) :
    ∀ v : Vertex,v≠59 → (relabel c e (Equiv.refl _) 59 v=palette 3 ↔ rawBrace r v=true) := by
  intro v hv
  have hn : e v≠mark := by rw [←hem];exact e.injective.ne hv
  have he : relabel c e (Equiv.refl _) 59 v=palette 3 ↔
      e v∈colorNeighborhood c (palette 3) mark := by
    change c (e 59) (e v)=palette 3 ↔ _
    rw [hem]
    constructor
    · intro h;exact (mem_colorNeighborhood _ _ _ _).mpr ⟨hn,h⟩
    · intro h;exact ((mem_colorNeighborhood _ _ _ _).mp h).2
  rw [he,neighborhood_union c hc root mark hm,brace_set]
  simp only [mem_insert,mem_union,hfree,hfake,hreal]
  have hroot : e v=root ↔ v=0 := by rw [←he0];exact e.injective.eq_iff
  rw [hroot]

#print axioms membership_after_placement
end UniformK60.BalancedHostBraceMembership
