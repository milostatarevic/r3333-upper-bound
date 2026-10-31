import UniformK60.Profiles
import Ramsey61.ClassificationAdapter

/-! Critical catalogue completeness on actual K60 neighborhoods. The generic
classification theorems are reused; every vertex in a physical map belongs
to the original host. -/
set_option autoImplicit false
namespace UniformK60.ClassificationAdapter
open Ramsey61

abbrev toLegacy {V C : Type*} (c : EdgeColoring V C) :=
  Ramsey61.ClassificationAdapter.toLegacy c
abbrev fromLegacy {V C : Type*} (c : R4333.EdgeColoring V C) :=
  Ramsey61.ClassificationAdapter.fromLegacy c

@[simp] theorem toLegacy_apply {V C : Type*} (c : EdgeColoring V C) (u v : V) :
    toLegacy c u v = c u v := rfl

/-- A complete map from a critical template into one actual monochromatic
neighborhood. Every template vertex is physical and all neighborhood
vertices occur. The palette names exactly the three other host colors. -/
structure PhysicalNeighborhoodMap (c : Host) (root : Fin 60) (q : FourColor)
    {n : Nat} (template : R4333.EdgeColoring (Fin n) (Fin 3)) where
  vertex : Fin n ↪ Fin 60
  mem_neighborhood : ∀ i, vertex i ∈ colorNeighborhood c q root
  covers_neighborhood : ∀ v ∈ colorNeighborhood c q root, ∃ i, vertex i = v
  colors : Fin 3 ≃ {r : FourColor // r ≠ q}
  map_color : ∀ i j, i ≠ j → c (vertex i) (vertex j) = (colors (template i j)).val

/-- The complete physical map is an equivalence with the actual neighborhood. -/
noncomputable def PhysicalNeighborhoodMap.neighborhoodEquiv
    {c : Host} {root : Fin 60} {q : FourColor} {n : Nat}
    {template : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c root q template) :
    Fin n ≃ {v // v ∈ colorNeighborhood c q root} :=
  Equiv.ofBijective (fun i => ⟨m.vertex i, m.mem_neighborhood i⟩)
    ⟨fun _ _ h => m.vertex.injective (congrArg Subtype.val h), by
      intro v
      obtain ⟨i, hi⟩ := m.covers_neighborhood v.val v.property
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem PhysicalNeighborhoodMap.neighborhoodEquiv_val
    {c : Host} {root : Fin 60} {q : FourColor} {n : Nat}
    {template : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c root q template) (i : Fin n) :
    (m.neighborhoodEquiv i).val = m.vertex i := rfl

/-- Expose the physical host vertices in a legacy weak neighborhood map. -/
noncomputable def physicalMapOfWeak (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 60) (q : FourColor) {n : Nat}
    (template : R4333.EdgeColoring (Fin n) (Fin 3))
    (e : R4333.WeakColorEquiv
      (R4333.neighborhoodThreeColoring (toLegacy c) hc q root) template) :
    PhysicalNeighborhoodMap c root q template where
  vertex :=
    { toFun := fun i => (e.vertex.symm i).val
      inj' := fun _ _ h => e.vertex.symm.injective (Subtype.ext h) }
  mem_neighborhood := fun i => (e.vertex.symm i).property
  covers_neighborhood := by
    intro v hv
    let x : R4333.NeighborhoodVertex (toLegacy c) q root := ⟨v, hv⟩
    refine ⟨e.vertex x, ?_⟩
    change (e.vertex.symm (e.vertex x)).val = v
    simp only [Equiv.symm_apply_apply]
    rfl
  colors := e.colors.symm
  map_color := by
    intro i j hij
    change c (e.vertex.symm i).val (e.vertex.symm j).val =
      (e.colors.symm (template i j)).val
    have hne : e.vertex.symm i ≠ e.vertex.symm j := e.vertex.symm.injective.ne hij
    have he := e.map_color (e.vertex.symm i) (e.vertex.symm j) hne
    simp only [Equiv.apply_symm_apply] at he
    have hcolor := congrArg e.colors.symm he
    simp only [Equiv.symm_apply_apply] at hcolor
    have hval := congrArg Subtype.val hcolor
    simpa only [R4333.neighborhoodThreeColoring_coe_apply_of_ne _ _ _ _ _ _ hne,
      toLegacy_apply] using hval

theorem physical_neighborhood_catalogued (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 60) (q : FourColor) {n : Nat} (hdegree : colorDegree c q root = n)
    (catalogue : List (R4333.EdgeColoring (Fin n) (Fin 3)))
    (hcomplete : R4333.ThreeColorCatalogueComplete n catalogue) :
    ∃ template ∈ catalogue, Nonempty (PhysicalNeighborhoodMap c root q template) := by
  obtain ⟨template, ht, ⟨e⟩⟩ := R4333.neighborhood_classified_of_degree
    (toLegacy c) hc q root hdegree catalogue hcomplete
  exact ⟨template, ht, ⟨physicalMapOfWeak c hc root q template e⟩⟩

/-- No catalogue completeness assumption remains at the physical K15 endpoint. -/
theorem physical_neighborhood_k15 (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 60) (q : FourColor) (hdegree : colorDegree c q root = 15) :
    ∃ template ∈ R4333.k15CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template) :=
  physical_neighborhood_catalogued c hc root q hdegree _ R4333.k15CriticalCatalogue_complete

/-- No catalogue completeness assumption remains at the physical K16 endpoint. -/
theorem physical_neighborhood_k16 (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 60) (q : FourColor) (hdegree : colorDegree c q root = 16) :
    ∃ template ∈ R4333.k16CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template) :=
  physical_neighborhood_catalogued c hc root q hdegree _ R4333.k16CriticalCatalogue_complete

/-- Every actual high neighborhood has a complete physical critical map. -/
theorem physical_high_neighborhood (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 60) (q : FourColor) (hhigh : 15 ≤ colorDegree c q root) :
    (colorDegree c q root = 15 ∧ ∃ template ∈ R4333.k15CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template)) ∨
    (colorDegree c q root = 16 ∧ ∃ template ∈ R4333.k16CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template)) := by
  have hupper := fourColor_colorDegree_le_sixteen c hc q root
  have hcases : colorDegree c q root = 15 ∨ colorDegree c q root = 16 := by omega
  rcases hcases with h15 | h16
  · exact Or.inl ⟨h15, physical_neighborhood_k15 c hc root q h15⟩
  · exact Or.inr ⟨h16, physical_neighborhood_k16 c hc root q h16⟩


#print axioms physical_neighborhood_k15
#print axioms physical_neighborhood_k16
#print axioms physical_high_neighborhood
end UniformK60.ClassificationAdapter
