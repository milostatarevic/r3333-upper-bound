import Ramsey61.Selector
import R4333Lean.CriticalCatalogues

/-!
# Reuse of the project's proved critical catalogues on the actual host

The legacy catalogue namespace has the same coloring data and the same
four-color type as `Ramsey61`. This module transports those definitions,
then obtains physical neighborhood maps from the proved completeness
theorems. No published catalogue theorem or solver answer is an axiom.
-/

namespace Ramsey61.ClassificationAdapter

def toLegacy {V C : Type*} (c : EdgeColoring V C) : R4333.EdgeColoring V C where
  color := c.color
  color_symm := c.color_symm

def fromLegacy {V C : Type*} (c : R4333.EdgeColoring V C) : EdgeColoring V C where
  color := c.color
  color_symm := c.color_symm

@[simp] theorem toLegacy_apply {V C : Type*} (c : EdgeColoring V C) (u v : V) :
    toLegacy c u v = c u v := rfl

@[simp] theorem fromLegacy_apply {V C : Type*} (c : R4333.EdgeColoring V C) (u v : V) :
    fromLegacy c u v = c u v := rfl

@[simp] theorem toLegacy_good {V C : Type*} (c : EdgeColoring V C) :
    R4333.NoMonochromaticTriangle (toLegacy c) ↔ NoMonochromaticTriangle c := Iff.rfl

@[simp] theorem fromLegacy_good {V C : Type*} (c : R4333.EdgeColoring V C) :
    NoMonochromaticTriangle (fromLegacy c) ↔ R4333.NoMonochromaticTriangle c := Iff.rfl

@[simp] theorem toLegacy_neighborhood {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (q : C) (v : V) :
    R4333.colorNeighborhood (toLegacy c) q v = colorNeighborhood c q v := rfl

@[simp] theorem toLegacy_degree {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (c : EdgeColoring V C) (q : C) (v : V) :
    R4333.colorDegree (toLegacy c) q v = colorDegree c q v := rfl

/-- Completeness covers every good modern K16 coloring, not only the
literal representatives. The witness retains its vertex and palette maps. -/
theorem k16_catalogued (c : EdgeColoring (Fin 16) (Fin 3))
    (hc : NoMonochromaticTriangle c) :
    ∃ t ∈ R4333.k16CriticalCatalogue,
      Nonempty (R4333.WeakColorEquiv (toLegacy c) t) :=
  R4333.k16CriticalCatalogue_complete.2 (toLegacy c) hc

theorem k15_catalogued (c : EdgeColoring (Fin 15) (Fin 3))
    (hc : NoMonochromaticTriangle c) :
    ∃ t ∈ R4333.k15CriticalCatalogue,
      Nonempty (R4333.WeakColorEquiv (toLegacy c) t) :=
  R4333.k15CriticalCatalogue_complete.2 (toLegacy c) hc

/-- The canonical local extension is not an extra vertex of the K61 host. -/
theorem k15_extends_to_k16 (c : EdgeColoring (Fin 15) (Fin 3))
    (hc : NoMonochromaticTriangle c) :
    ∃ d : EdgeColoring (Fin 16) (Fin 3), NoMonochromaticTriangle d ∧
      ∃ vertex : Fin 15 ↪ Fin 16, ∃ colors : Fin 3 ≃ Fin 3,
        ∀ u v, u ≠ v → colors (c u v) = d (vertex u) (vertex v) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := R4333.everyThreeColoringExtends_15_16 (toLegacy c) hc
  exact ⟨fromLegacy d, hd, e.vertex, e.colors, e.map_color⟩

theorem k16_colorGraph_srg (c : EdgeColoring (Fin 16) (Fin 3))
    (hc : NoMonochromaticTriangle c) (q : Fin 3) :
    letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
    (colorGraph c q).IsSRGWith 16 5 0 2 := by
  classical
  have hdec : R4333.colorGraphDecidableRel (toLegacy c) q =
      Classical.decRel (colorGraph c q).Adj := Subsingleton.elim _ _
  have h := R4333.k16_colorGraph_isSRG (toLegacy c) hc q
  change @SimpleGraph.IsSRGWith (Fin 16) _ (colorGraph c q)
    (R4333.colorGraphDecidableRel (toLegacy c) q) 16 5 0 2 at h
  rw [hdec] at h
  exact h

/-- A complete map from a critical template into one actual monochromatic
neighborhood. Every template vertex is physical and all neighborhood
vertices occur. The palette names exactly the three other host colors. -/
structure PhysicalNeighborhoodMap (c : Host) (root : Fin 61) (q : FourColor)
    {n : Nat} (template : R4333.EdgeColoring (Fin n) (Fin 3)) where
  vertex : Fin n ↪ Fin 61
  mem_neighborhood : ∀ i, vertex i ∈ colorNeighborhood c q root
  covers_neighborhood : ∀ v ∈ colorNeighborhood c q root, ∃ i, vertex i = v
  colors : Fin 3 ≃ {r : FourColor // r ≠ q}
  map_color : ∀ i j, i ≠ j → c (vertex i) (vertex j) = (colors (template i j)).val

/-- Expose the physical host vertices in a legacy weak neighborhood map. -/
noncomputable def physicalMapOfWeak (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (q : FourColor) {n : Nat}
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
    (root : Fin 61) (q : FourColor) {n : Nat} (hdegree : colorDegree c q root = n)
    (catalogue : List (R4333.EdgeColoring (Fin n) (Fin 3)))
    (hcomplete : R4333.ThreeColorCatalogueComplete n catalogue) :
    ∃ template ∈ catalogue, Nonempty (PhysicalNeighborhoodMap c root q template) := by
  obtain ⟨template, ht, ⟨e⟩⟩ := R4333.neighborhood_classified_of_degree
    (toLegacy c) hc q root hdegree catalogue hcomplete
  exact ⟨template, ht, ⟨physicalMapOfWeak c hc root q template e⟩⟩

/-- No catalogue completeness assumption remains at the physical K15 endpoint. -/
theorem physical_neighborhood_k15 (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (q : FourColor) (hdegree : colorDegree c q root = 15) :
    ∃ template ∈ R4333.k15CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template) :=
  physical_neighborhood_catalogued c hc root q hdegree _ R4333.k15CriticalCatalogue_complete

/-- No catalogue completeness assumption remains at the physical K16 endpoint. -/
theorem physical_neighborhood_k16 (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (q : FourColor) (hdegree : colorDegree c q root = 16) :
    ∃ template ∈ R4333.k16CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template) :=
  physical_neighborhood_catalogued c hc root q hdegree _ R4333.k16CriticalCatalogue_complete

/-- Every actual high neighborhood has a complete physical critical map. -/
theorem physical_high_neighborhood (c : Host) (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (q : FourColor) (hhigh : 15 ≤ colorDegree c q root) :
    (colorDegree c q root = 15 ∧ ∃ template ∈ R4333.k15CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template)) ∨
    (colorDegree c q root = 16 ∧ ∃ template ∈ R4333.k16CriticalCatalogue,
      Nonempty (PhysicalNeighborhoodMap c root q template)) := by
  have hupper := fourColor_colorDegree_le_sixteen c hc q root
  have hcases : colorDegree c q root = 15 ∨ colorDegree c q root = 16 := by omega
  rcases hcases with h15 | h16
  · exact Or.inl ⟨h15, physical_neighborhood_k15 c hc root q h15⟩
  · exact Or.inr ⟨h16, physical_neighborhood_k16 c hc root q h16⟩

#print axioms Ramsey61.ClassificationAdapter.k16_catalogued
#print axioms Ramsey61.ClassificationAdapter.k15_catalogued
#print axioms Ramsey61.ClassificationAdapter.k15_extends_to_k16
#print axioms Ramsey61.ClassificationAdapter.k16_colorGraph_srg
#print axioms Ramsey61.ClassificationAdapter.physical_neighborhood_k15
#print axioms Ramsey61.ClassificationAdapter.physical_neighborhood_k16
#print axioms Ramsey61.ClassificationAdapter.physical_high_neighborhood

end Ramsey61.ClassificationAdapter
