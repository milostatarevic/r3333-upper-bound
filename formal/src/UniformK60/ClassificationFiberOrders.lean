import UniformK60.ClassificationSupportOrders
import UniformK60.ClassificationFixedPalette
import UniformK60.ClassificationGeometry
import UniformK60.PhysicalHelpers

set_option autoImplicit false
namespace UniformK60.ClassificationFiberOrders
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette
open UniformK60.ClassificationGeometry UniformK60.ClassificationSupportOrders

/-- A complete physical template map identifies each of its root-color
neighborhoods with the entire corresponding physical attaching support. -/
theorem template_fiber_image {n : Nat} {c : Host} {mark root : Vertex}
    {q : FourColor} {template : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c mark q template)
    (v : Fin n) (hv : m.vertex v = root) (p : Fin 3) :
    (R4333.colorNeighborhood template p v).image m.vertex =
      attachingSupport c root q mark (m.colors p).val := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
    have hj' := (R4333.mem_colorNeighborhood _ _ _ _).mp hj
    apply mem_inter.mpr
    refine ⟨m.mem_neighborhood j, (mem_colorNeighborhood _ _ _ _).mpr ⟨?_, ?_⟩⟩
    · rw [← hv]
      exact m.vertex.injective.ne hj'.1
    · rw [← hv, m.map_color v j hj'.1.symm, hj'.2]
  · intro hw
    obtain ⟨hmark, hroot⟩ := mem_inter.mp hw
    obtain ⟨j, rfl⟩ := m.covers_neighborhood w hmark
    have hroot' := (mem_colorNeighborhood _ _ _ _).mp hroot
    have hj : j ≠ v := by intro he; subst j; exact hroot'.1 hv
    refine mem_image.mpr ⟨j, (R4333.mem_colorNeighborhood _ _ _ _).mpr ⟨hj, ?_⟩, rfl⟩
    apply m.colors.injective
    apply Subtype.ext
    have he := m.map_color v j hj.symm
    rw [hv] at he
    exact he.symm.trans hroot'.2

/-- Transport an exact ordered template fiber to the physical host. -/
theorem realize_fiber_order {n k : Nat} {c : Host} {mark root : Vertex}
    {q : FourColor} {template : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c mark q template)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) (hp : m.colors = pal)
    (v : Fin n) (hv : m.vertex v = root) (p a : Fin 3)
    (order : Fin k → Fin n) (adj : Fin k → Fin k → Prop)
    (hinj : Function.Injective order)
    (himage : univ.image order = R4333.colorNeighborhood template p v)
    (hpattern : ∀ i j, i ≠ j → (template (order i) (order j) = a ↔ adj i j)) :
    (attachingSupport c root q mark (pal p).val).card = k ∧
    ∃ e : Fin k ↪ Vertex,
      univ.image e = attachingSupport c root q mark (pal p).val ∧
      ∀ i j, i ≠ j → (c (e i) (e j) = (pal a).val ↔ adj i j) := by
  let e : Fin k ↪ Vertex := ⟨m.vertex ∘ order, m.vertex.injective.comp hinj⟩
  have he : univ.image e = attachingSupport c root q mark (pal p).val := by
    change univ.image (m.vertex ∘ order) = _
    rw [← image_image, himage, template_fiber_image m v hv p, hp]
  refine ⟨?_, e, he, ?_⟩
  · rw [← he, card_image_of_injective _ e.injective]
    simp
  · intro i j hij
    change c (m.vertex (order i)) (m.vertex (order j)) = (pal a).val ↔ adj i j
    rw [m.map_color _ _ (hinj.ne hij), hp]
    have hinjpal : (pal (template (order i) (order j))).val = (pal a).val ↔
        template (order i) (order j) = a := by
      constructor
      · intro h
        exact pal.injective (Subtype.ext h)
      · intro h
        rw [h]
    exact hinjpal.trans (hpattern i j hij)

/-- Every foreign root-color fiber of an actual critical neighborhood is a
complete physical P4 or C5 in either chosen remaining color. -/
theorem physical_fiber_ordered (c : Host) (hc : NoMonochromaticTriangle c)
    (mark root : Vertex) (q : FourColor)
    (hr : root ∈ colorNeighborhood c q mark) (hh : 15 ≤ colorDegree c q mark)
    (p a : FourColor) (hpq : p ≠ q) (haq : a ≠ q) (hap : a ≠ p) :
    ((attachingSupport c root q mark p).card = 4 ∧
      ∃ e : Fin 4 ↪ Vertex, univ.image e = attachingSupport c root q mark p ∧
        ∀ i j, i ≠ j → (c (e i) (e j) = a ↔ PathAdjacent i j)) ∨
    ((attachingSupport c root q mark p).card = 5 ∧
      ∃ e : Fin 5 ↪ Vertex, univ.image e = attachingSupport c root q mark p ∧
        ∀ i j, i ≠ j → (c (e i) (e j) = a ↔ CycleAdjacent i j)) := by
  obtain ⟨qi, rfl⟩ := palette_surjective q
  let pal := foreignEquiv qi
  let lp : Fin 3 := pal.symm ⟨p, hpq⟩
  let la : Fin 3 := pal.symm ⟨a, haq⟩
  have hpp : (pal lp).val = p := congrArg Subtype.val (pal.apply_symm_apply ⟨p, hpq⟩)
  have haa : (pal la).val = a := congrArg Subtype.val (pal.apply_symm_apply ⟨a, haq⟩)
  have hne : lp ≠ la := by
    intro h
    exact hap (haa.symm.trans ((congrArg (fun z => (pal z).val) h).symm.trans hpp))
  have hu := fourColor_colorDegree_le_sixteen c hc (palette qi) mark
  have cases : colorDegree c (palette qi) mark = 15 ∨ colorDegree c (palette qi) mark = 16 := by omega
  rcases cases with h15 | h16
  · obtain ⟨t, m, hm⟩ := physical_k15_fixed_palette c hc mark (palette qi) h15 pal
    obtain ⟨v, hv⟩ := m.covers_neighborhood root hr
    rcases minor_degrees t v lp with h4 | h5
    · obtain ⟨hi, he, hp⟩ := minor_path t v lp la hne h4
      have result := realize_fiber_order m pal hm v hv lp la
        (minorPathOrder t v lp la) PathAdjacent hi he hp
      exact Or.inl (by simpa only [hpp, haa] using result)
    · obtain ⟨hi, he, hp⟩ := minor_cycle t v lp la hne h5
      have result := realize_fiber_order m pal hm v hv lp la
        (minorCycleOrder t v lp la) CycleAdjacent hi he hp
      exact Or.inr (by simpa only [hpp, haa] using result)
  · obtain ⟨t, m, hm⟩ := physical_k16_fixed_palette c hc mark (palette qi) h16 pal
    obtain ⟨v, hv⟩ := m.covers_neighborhood root hr
    obtain ⟨hi, he, hp⟩ := full_cycle t v lp la hne (full_degrees t v lp)
    have result := realize_fiber_order m pal hm v hv lp la
      (fullCycleOrder t v lp la) CycleAdjacent hi he hp
    exact Or.inr (by simpa only [hpp, haa] using result)

#print axioms physical_fiber_ordered
end UniformK60.ClassificationFiberOrders
