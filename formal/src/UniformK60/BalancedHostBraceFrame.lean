import UniformK60.BalancedHostBraceGeometry
import UniformK60.ThreeSupportFrame

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.BalancedHostBraceFrame
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette
open UniformK60.ClassificationGeometry UniformK60.ClassificationSupportConsumers
open UniformK60.ClassificationFiberOrders UniformK60.ClassificationSupportOrders
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedGeometry UniformK60.BalancedHostBraceGeometry
open UniformK60.ThreeSupportFrame CompletionC.NativeMatrices

private theorem cycle_same : ∀ i j : Fin 5,
    CycleAdjacent i j ↔ PricingC.Rooted45Orientation.Cycle 5 i.val j.val := by decide

/-- Enumerate an entire actual attaching support; no support vertex is lost. -/
noncomputable def enumerate {c : Host} {root mark : Vertex} {q : Color} {n : Nat}
    (h : (support c root mark q).card=n) : Fin n ↪ Vertex := by
  classical
  let S := support c root mark q
  let e : S≃Fin n := Fintype.equivFinOfCardEq (by simpa [S] using h)
  exact ⟨fun i => (e.symm i).val,fun i j hh => e.symm.injective (Subtype.ext hh)⟩

theorem enumerate_image {c : Host} {root mark : Vertex} {q : Color} {n : Nat}
    (h : (support c root mark q).card=n) : univ.image (enumerate h)=support c root mark q := by
  classical
  let S := support c root mark q
  let e : S≃Fin n := Fintype.equivFinOfCardEq (by simpa [S] using h)
  ext v
  constructor
  · rintro hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact (e.symm i).property
  · intro hv
    exact mem_image.mpr ⟨e ⟨v,hv⟩,mem_univ _,by
      change (e.symm (e ⟨v,hv⟩)).val=v
      simp⟩

theorem image_mem {c : Host} {root mark : Vertex} {q : Color} {n : Nat}
    (e : Fin n↪Vertex) (he : univ.image e=support c root mark q) (i : Fin n) :
    e i∈support c root mark q := by rw [←he];exact mem_image.mpr ⟨i,mem_univ _,rfl⟩

/-- Only the actual five-vertex fake support is ordered as a pentagon. -/
theorem fake_cycle (c : Host) (hc : NoMonochromaticTriangle c) (root mark : Vertex)
    (hm : mark∈colorNeighborhood c (palette 3) root)
    (hh : 15≤colorDegree c (palette 3) mark) (h5 : (support c root mark 1).card=5) :
    ∃ e : Fin 5↪Vertex,univ.image e=support c root mark 1 ∧
      ∀ i j,i≠j → c (e i) (e j)=
        (if PricingC.Rooted45Orientation.Cycle 5 i.val j.val then palette 0 else palette 2) := by
  have hr : root∈colorNeighborhood c (palette 3) mark := by
    apply (mem_colorNeighborhood _ _ _ _).mpr
    have h := (mem_colorNeighborhood _ _ _ _).mp hm
    exact ⟨h.1.symm,(c.color_symm mark root).trans h.2⟩
  obtain h|⟨_,e,he,hcycle⟩ := physical_fiber_ordered c hc mark root (palette 3) hr hh
    (palette 1) (palette 0) (by decide) (by decide) (by decide)
  · change (support c root mark 1).card=4 ∧ _ at h
    omega
  refine ⟨e,he,?_⟩
  intro i j hij
  have hi := mem_inter.mp (image_mem e he i)
  have hj := mem_inter.mp (image_mem e he j)
  have h1 : c (e i) (e j)≠palette 1 := neighborhood_avoids_own_color c hc hi.2 hj.2 (e.injective.ne hij)
  have h3 : c (e i) (e j)≠palette 3 := neighborhood_avoids_own_color c hc hi.1 hj.1 (e.injective.ne hij)
  by_cases hcy : PricingC.Rooted45Orientation.Cycle 5 i.val j.val
  · rw [if_pos hcy]
    exact (hcycle i j hij).mpr ((cycle_same i j).mpr hcy)
  · rw [if_neg hcy]
    have h0 : c (e i) (e j)≠palette 0 := fun hh => hcy ((cycle_same i j).mp ((hcycle i j hij).mp hh))
    obtain ⟨q,hq⟩ := palette_surjective (c (e i) (e j))
    rw [←hq] at h0 h1 h3 ⊢
    fin_cases q <;> try contradiction
    rfl

def castReal {c : Host} {root : Vertex} {a b : Bool} (h : a=b)
    (m : PhysicalNeighborhoodMap c root (palette 2) (R4333.k16Template a)) :
    PhysicalNeighborhoodMap c root (palette 2) (R4333.k16Template b) where
  vertex := m.vertex
  mem_neighborhood := m.mem_neighborhood
  covers_neighborhood := m.covers_neighborhood
  colors := m.colors
  map_color i j hij := by rw [←h];exact m.map_color i j hij

/-- Normalize the complete real16 template while retaining its entire
physical support. The resulting geometry is one of the nine checked rows. -/
theorem normalize_real {c : Host} {root mark : Vertex} {t : Bool}
    (m : PhysicalNeighborhoodMap c root (palette 2) (R4333.k16Template t))
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) root)
    (hp : m.colors=foreignEquiv 2) (hh : 15≤colorDegree c (palette 3) mark)
    (s : Shape) (hs : AllowedShape s) (hcard : (support c root mark 2).card=s.right) :
    ∃ g : Geometry,geometryShape g=s ∧
      ∃ n : PhysicalNeighborhoodMap c root (palette 2) (R4333.k16Template (geometryKind g)),
        n.colors=foreignEquiv 2 ∧
        ClassificationSupports.support (side:=true) n mark=geometrySupport g := by
  have hmcard : (ClassificationSupports.support (side:=true) m mark).card=s.right := by
    have he := congrArg Finset.card (ClassificationSupports.support_image (side:=true) m hm)
    rw [card_image_of_injective _ m.vertex.injective] at he
    exact he.trans hcard
  cases t
  · rcases actual_u16_support_admitted (side:=true) m hc hm hp hh with h|h
    · obtain ⟨h4,rep,hrep,n,hn,hns⟩ := h
      have hr : s.right=4 := hmcard.symm.trans h4
      have hrep' : rep∈representatives s false := by simpa [representatives,hr] using hrep
      obtain ⟨g,hg,hkind,hset⟩ := admitted_geometry s hs false rep hrep'
      refine ⟨g,hg,castReal hkind.symm n,hn,?_⟩
      change ClassificationSupports.support (side:=true) n mark=geometrySupport g
      rw [hset]
      exact hns
    · obtain ⟨h5,rep,hrep,n,hn,hns⟩ := h
      have hr : s.right=5 := hmcard.symm.trans h5
      have hrep' : rep∈representatives s false := by simpa [representatives,hr] using hrep
      obtain ⟨g,hg,hkind,hset⟩ := admitted_geometry s hs false rep hrep'
      refine ⟨g,hg,castReal hkind.symm n,hn,?_⟩
      change ClassificationSupports.support (side:=true) n mark=geometrySupport g
      rw [hset]
      exact hns
  · rcases actual_t16_support_admitted (side:=true) m hc hm hp hh with h|h
    · obtain ⟨h4,rep,hrep,n,hn,hns⟩ := h
      have hr : s.right=4 := hmcard.symm.trans h4
      have hrep' : rep∈representatives s true := by simpa [representatives,hr] using hrep
      obtain ⟨g,hg,hkind,hset⟩ := admitted_geometry s hs true rep hrep'
      refine ⟨g,hg,castReal hkind.symm n,hn,?_⟩
      change ClassificationSupports.support (side:=true) n mark=geometrySupport g
      rw [hset]
      exact hns
    · obtain ⟨h5,rep,hrep,n,hn,hns⟩ := h
      have hr : s.right=5 := hmcard.symm.trans h5
      have hrep' : rep∈representatives s true := by simpa [representatives,hr] using hrep
      obtain ⟨g,hg,hkind,hset⟩ := admitted_geometry s hs true rep hrep'
      refine ⟨g,hg,castReal hkind.symm n,hn,?_⟩
      change ClassificationSupports.support (side:=true) n mark=geometrySupport g
      rw [hset]
      exact hns

structure ActualFrame (c : Host) (root mark : Vertex) (g : Geometry) where
  real : PhysicalNeighborhoodMap c root (palette 2) (R4333.k16Template (geometryKind g))
  real_palette : real.colors=foreignEquiv 2
  real_support : ClassificationSupports.support (side:=true) real mark=geometrySupport g
  frame : Frame c (geometryShape g).free (geometryShape g).left (geometryShape g).right
  root_eq : frame.root=root
  mark_eq : frame.mark=mark
  free_image : univ.image frame.free=support c root mark 0
  fake_image : univ.image frame.left=support c root mark 1
  real_vertex : ∀ j,frame.right j=real.vertex (realOrder g j)

theorem reindex_image {a b : Nat} (e : Fin a≃Fin b) (f : Fin b↪Vertex) :
    univ.image (e.toEmbedding.trans f)=univ.image f := by
  ext v
  constructor
  · rintro hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨e i,mem_univ _,rfl⟩
  · rintro hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨e.symm i,mem_univ _,by simp⟩

noncomputable def of_orders {c : Host} {root mark : Vertex} (g : Geometry)
    (m : PhysicalNeighborhoodMap c root (palette 2) (R4333.k16Template (geometryKind g)))
    (hp : m.colors=foreignEquiv 2)
    (hm : mark∈colorNeighborhood c (palette 3) root)
    (hs : ClassificationSupports.support (side:=true) m mark=geometrySupport g)
    (free : Fin (geometryShape g).free↪Vertex)
    (hfree : univ.image free=support c root mark 0)
    (fake : Fin 5↪Vertex) (hfake : univ.image fake=support c root mark 1)
    (edges : ∀ i j,i≠j → c (fake i) (fake j)=
      (if PricingC.Rooted45Orientation.Cycle 5 i.val j.val then palette 0 else palette 2)) :
    ActualFrame c root mark g := by
  let fake' := (finCongr (geometry_dimensions g).1).toEmbedding.trans fake
  have hfake' : univ.image fake'=support c root mark 1 :=
    (reindex_image _ _).trans hfake
  let real : Fin (geometryShape g).right↪Vertex :=
    ⟨fun i => m.vertex (realOrder g i),m.vertex.injective.comp (realOrder_injective g)⟩
  have hreal (i : Fin (geometryShape g).right) :
      realOrder g i∈ClassificationSupports.support (side:=true) m mark := by
    rw [hs]
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  let f : Frame c (geometryShape g).free (geometryShape g).left (geometryShape g).right :=
    { root := root
      mark := mark
      free := free
      left := fake'
      right := real
      mark_mem := hm
      free_mem i := (mem_inter.mp (image_mem free hfree i)).2
      left_mem i := (mem_inter.mp (image_mem fake' hfake' i)).2
      right_mem i := m.mem_neighborhood _
      marked_free i := ((mem_colorNeighborhood _ _ _ _).mp
        (mem_inter.mp (image_mem free hfree i)).1).2
      marked_left i := ((mem_colorNeighborhood _ _ _ _).mp
        (mem_inter.mp (image_mem fake' hfake' i)).1).2
      marked_right i := (mem_filter.mp (hreal i)).2
      left_edges i j hij := by
        have h := edges ((finCongr (geometry_dimensions g).1) i)
          ((finCongr (geometry_dimensions g).1) j)
          ((finCongr (geometry_dimensions g).1).injective.ne hij)
        simpa only [fake',Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
          finCongr_apply,Fin.coe_cast,(geometry_dimensions g).1] using h
      right_edges i j hij := by
        change c (m.vertex (realOrder g i)) (m.vertex (realOrder g j))=_
        rw [m.map_color _ _ ((realOrder_injective g).ne hij),hp,realOrder_edges g i j hij]
        split_ifs <;> rfl }
  exact ⟨m,hp,hs,f,rfl,rfl,hfree,hfake',fun _ => rfl⟩

/-- Actual critical geometry produces one of the nine full-real-template
frames, with both low supports still consisting solely of actual vertices. -/
theorem actual_frame (c : Host) (hc : NoMonochromaticTriangle c) (root mark : Vertex)
    (hm : mark∈colorNeighborhood c (palette 3) root)
    (hh : 15≤colorDegree c (palette 3) mark)
    (hreal : colorDegree c (palette 2) root=16)
    (hfake : (support c root mark 1).card=5) :
    ∃ g : Geometry,Nonempty (ActualFrame c root mark g) := by
  obtain ⟨s,hs,hfree,hrealcard⟩ := oriented_shape c hc root mark hm hh hfake
  obtain ⟨t,m,hp⟩ := physical_k16_fixed_palette c hc root (palette 2) hreal (foreignEquiv 2)
  obtain ⟨g,hg,n,hn,hns⟩ := normalize_real m hc hm hp hh s hs hrealcard
  have hfree' : (support c root mark 0).card=(geometryShape g).free := by rw [hg];exact hfree
  obtain ⟨fake,hfake,hedges⟩ := fake_cycle c hc root mark hm hh hfake
  exact ⟨g,⟨of_orders g n hn hm hns (enumerate hfree') (enumerate_image hfree') fake hfake hedges⟩⟩

#print axioms actual_frame
end UniformK60.BalancedHostBraceFrame
