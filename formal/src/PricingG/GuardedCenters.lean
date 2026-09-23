import PricingG.PhysicalBlocks

namespace PricingG
open Finset Ramsey61

private theorem different_cells_not_mem (c : Host) (r : Fin 61)
    (p q : FourColor) (hpq : p ≠ q) {y : Fin 61}
    (hy : y ∈ colorNeighborhood c q r) : y ∉ colorNeighborhood c p r := by
  intro hx
  exact hpq (((mem_colorNeighborhood _ _ _ _).mp hx).2.symm.trans
    ((mem_colorNeighborhood _ _ _ _).mp hy).2)

private theorem cross_fiber_card {c : Host} {r : Fin 61} {p : FourColor}
    (X : PhysicalBlock c r p) (q : FourColor) (y : Fin 61)
    (hout : y ∉ colorNeighborhood c p r) :
    (univ.filter fun i => c (X.map.vertex i) y = q).card =
      (colorNeighborhood c q y ∩ colorNeighborhood c p r).card := by
  rw [X.physical_filter_card (fun z => c z y = q)]
  congr 1
  ext z
  constructor
  · intro h
    have hz := (mem_filter.mp h).1
    have hzy : z ≠ y := by intro he; subst z; exact hout hz
    exact mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr
      ⟨hzy,by rw [c.color_symm]; exact (mem_filter.mp h).2⟩,hz⟩
  · intro h
    refine mem_filter.mpr ⟨(mem_inter.mp h).2,?_⟩
    rw [c.color_symm]
    exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp h).1).2

/-- Exact local mask in the actual two root blocks. Both the possible formal
completion point and independent local recolorings are absent from the result. -/
theorem physical_block_mask {c : Host} {r : Fin 61} {p q : FourColor}
    (X : PhysicalBlock c r p) (Y : PhysicalBlock c r q)
    (hc : NoMonochromaticTriangle c) (hpq : p ≠ q) (x y : Fin 16)
    (hhigh : 15 ≤ colorDegree c q (X.map.vertex x))
    (hcross : c (X.map.vertex x) (Y.map.vertex y) = q) :
    (((X.graph q hpq.symm).neighborFinset x).filter fun a =>
      c (X.map.vertex a) (Y.map.vertex y) = p).card = 2 ∨
    (((X.graph q hpq.symm).neighborFinset x).filter fun a =>
      c (X.map.vertex a) (Y.map.vertex y) = p).card = 5 := by
  classical
  let K := X.graph q hpq.symm
  let A := (K.neighborFinset x).image X.map.vertex
  have hA : A.card = 5 := by
    rw [card_image_of_injective _ X.map.vertex.injective,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact (X.graph_srg q hpq.symm).regular x
  have himage : A = colorNeighborhood c p r ∩ colorNeighborhood c q (X.map.vertex x) :=
    X.neighbor_image q hpq.symm x
  have houtX : Y.map.vertex y ∉ colorNeighborhood c p r :=
    different_cells_not_mem c r p q hpq (Y.map.mem_neighborhood y)
  have hyne : Y.map.vertex y ≠ X.map.vertex x := by
    intro h
    exact houtX (h ▸ X.map.mem_neighborhood x)
  have hy : Y.map.vertex y ∈ colorNeighborhood c q (X.map.vertex x) :=
    (mem_colorNeighborhood _ _ _ _).mpr ⟨hyne,hcross⟩
  have houtA : Y.map.vertex y ∉ A := by
    rw [himage]
    exact fun h => houtX (mem_inter.mp h).1
  have hind : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → c u v ≠ (Y.map.colors (Y.selectedColor p hpq)).val := by
    intro u hu v hv huv
    rw [Y.selectedColor_val]
    rw [himage] at hu hv
    exact neighborhood_avoids_own_color c hc (mem_inter.mp hu).1 (mem_inter.mp hv).1 huv
  have hm := PricingC.high_neighborhood_physical_mask c hc (X.map.vertex x) q hhigh
    Y.map.colors (Y.selectedColor p hpq) A hA
    (by rw [himage]; exact inter_subset_right) hind (Y.map.vertex y) hy houtA
  simp only [Y.selectedColor_val] at hm
  have hmap : ((K.neighborFinset x).filter fun a => c (X.map.vertex a) (Y.map.vertex y) = p).image X.map.vertex =
      A.filter (fun a => c a (Y.map.vertex y) = p) := by
    ext z
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨mem_image.mpr ⟨a,(mem_filter.mp ha).1,rfl⟩,(mem_filter.mp ha).2⟩
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp (mem_filter.mp h).1
      exact mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,(mem_filter.mp h).2⟩,rfl⟩
  have hcard := congrArg Finset.card hmap
  rw [card_image_of_injective _ X.map.vertex.injective] at hcard
  rwa [← hcard] at hm

/-- G constructs both complete physical neighborhood views and both genuine
fiber-center bijections. No local scope or multiplicity premise remains. -/
theorem regular_overlap_has_bijective_centers
    (c : Host) (hc : NoMonochromaticTriangle c) (r : Fin 61) (p q : FourColor)
    (hG : RegularOverlapGuard c r p q) :
    ∃ X : PhysicalBlock c r p, ∃ Y : PhysicalBlock c r q,
      ∃ f g : Fin 16 → Fin 16, Function.Bijective f ∧ Function.Bijective g ∧
      (∀ x y, (X.graph q hG.colors_distinct.symm).Adj (f y) x ↔
        c (X.map.vertex x) (Y.map.vertex y) = q) ∧
      (∀ x y, (Y.graph p hG.colors_distinct).Adj (g x) y ↔
        c (X.map.vertex x) (Y.map.vertex y) = p) := by
  classical
  obtain ⟨X⟩ := exists_physicalBlock c hc r p hG.first_root_degree
  obtain ⟨Y⟩ := exists_physicalBlock c hc r q hG.second_root_degree
  have hf : ∀ y : Fin 16, ∃ a, ∀ x, (X.graph q hG.colors_distinct.symm).Adj a x ↔
      c (X.map.vertex x) (Y.map.vertex y) = q := by
    intro y
    have hout := different_cells_not_mem c r p q hG.colors_distinct (Y.map.mem_neighborhood y)
    obtain ⟨a,ha,_⟩ := X.cross_fiber_unique_center hc q hG.colors_distinct.symm (Y.map.vertex y) hout
      (by rw [cross_fiber_card X q _ hout]; exact hG.second_fibers _ (Y.map.mem_neighborhood y))
    exact ⟨a,ha⟩
  have hg : ∀ x : Fin 16, ∃ b, ∀ y, (Y.graph p hG.colors_distinct).Adj b y ↔
      c (X.map.vertex x) (Y.map.vertex y) = p := by
    intro x
    have hout := different_cells_not_mem c r q p hG.colors_distinct.symm (X.map.mem_neighborhood x)
    obtain ⟨b,hb,_⟩ := Y.cross_fiber_unique_center hc p hG.colors_distinct (X.map.vertex x) hout
      (by rw [cross_fiber_card Y p _ hout]; exact hG.first_fibers _ (X.map.mem_neighborhood x))
    exact ⟨b,fun y => by simpa only [c.color_symm (Y.map.vertex y) (X.map.vertex x)] using hb y⟩
  choose f hf using hf
  choose g hg using hg
  have hd : ∀ x y, ¬((X.graph q hG.colors_distinct.symm).Adj (f y) x ∧
      (Y.graph p hG.colors_distinct).Adj (g x) y) := by
    intro x y h
    exact hG.colors_distinct (((hg x y).mp h.2).symm.trans ((hf y x).mp h.1))
  have hk : ∀ y x, (X.graph q hG.colors_distinct.symm).Adj (f y) x →
      (univ.filter fun a => (Y.graph p hG.colors_distinct).Adj (g a) y ∧
        (X.graph q hG.colors_distinct.symm).Adj x a).card = 2 ∨
      (univ.filter fun a => (Y.graph p hG.colors_distinct).Adj (g a) y ∧
        (X.graph q hG.colors_distinct.symm).Adj x a).card = 5 := by
    intro y x hxy
    have hm := physical_block_mask X Y hc hG.colors_distinct x y
      (hG.first_opposite_high _ (X.map.mem_neighborhood x)) ((hf y x).mp hxy)
    have heq : (univ.filter fun a => (Y.graph p hG.colors_distinct).Adj (g a) y ∧
        (X.graph q hG.colors_distinct.symm).Adj x a) =
        ((X.graph q hG.colors_distinct.symm).neighborFinset x).filter fun a =>
          c (X.map.vertex a) (Y.map.vertex y) = p := by
      ext a
      simp only [mem_filter,mem_univ,true_and,SimpleGraph.mem_neighborFinset,hg,and_comm]
    rwa [heq]
  have hl : ∀ x y, (Y.graph p hG.colors_distinct).Adj (g x) y →
      (univ.filter fun b => (X.graph q hG.colors_distinct.symm).Adj (f b) x ∧
        (Y.graph p hG.colors_distinct).Adj y b).card = 2 ∨
      (univ.filter fun b => (X.graph q hG.colors_distinct.symm).Adj (f b) x ∧
        (Y.graph p hG.colors_distinct).Adj y b).card = 5 := by
    intro x y hxy
    have hm := physical_block_mask Y X hc hG.colors_distinct.symm y x
      (hG.second_opposite_high _ (Y.map.mem_neighborhood y))
      (by rw [c.color_symm]; exact (hg x y).mp hxy)
    have heq : (univ.filter fun b => (X.graph q hG.colors_distinct.symm).Adj (f b) x ∧
        (Y.graph p hG.colors_distinct).Adj y b) =
        ((Y.graph p hG.colors_distinct).neighborFinset y).filter fun b =>
          c (Y.map.vertex b) (X.map.vertex x) = q := by
      ext b
      simp only [mem_filter,mem_univ,true_and,SimpleGraph.mem_neighborFinset,hf,
        c.color_symm (Y.map.vertex b) (X.map.vertex x),and_comm]
    rwa [heq]
  obtain ⟨hfb,hgb⟩ := centerMaps_bijective (X.graph q hG.colors_distinct.symm)
    (Y.graph p hG.colors_distinct) (X.graph_srg q hG.colors_distinct.symm)
    (Y.graph_srg p hG.colors_distinct) f g hd hk hl
  exact ⟨X,Y,f,g,hfb,hgb,fun x y => hf y x,hg⟩

#print axioms regular_overlap_has_bijective_centers
end PricingG
