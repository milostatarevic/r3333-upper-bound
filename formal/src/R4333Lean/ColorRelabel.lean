import R4333Lean.ThreeColorCatalogue

/-! Reusable transport of edge colourings along colour and vertex equivalences. -/

namespace R4333

/-- Apply a global colour equivalence without changing the vertices. -/
def mapEdgeColors {V C D : Type*} (c : EdgeColoring V C) (e : C ≃ D) :
    EdgeColoring V D where
  color u v := e (c u v)
  color_symm u v := by rw [c.color_symm]

@[simp] theorem mapEdgeColors_apply {V C D : Type*}
    (c : EdgeColoring V C) (e : C ≃ D) (u v : V) :
    mapEdgeColors c e u v = e (c u v) := rfl

/-- Pull an edge colouring back along a vertex equivalence. -/
def relabelVertices {V W C : Type*} (c : EdgeColoring V C) (e : W ≃ V) :
    EdgeColoring W C where
  color u v := c (e u) (e v)
  color_symm u v := by rw [c.color_symm]

@[simp] theorem relabelVertices_apply {V W C : Type*}
    (c : EdgeColoring V C) (e : W ≃ V) (u v : W) :
    relabelVertices c e u v = c (e u) (e v) := rfl

theorem noMono_mapEdgeColors {V C D : Type*}
    (c : EdgeColoring V C) (e : C ≃ D)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (mapEdgeColors c e) := by
  intro u v w hdistinct hmono
  apply hc u v w hdistinct
  exact ⟨e.injective hmono.1, e.injective hmono.2⟩

theorem noMono_relabelVertices {V W C : Type*}
    (c : EdgeColoring V C) (e : W ≃ V)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (relabelVertices c e) := by
  intro u v w hdistinct hmono
  apply hc (e u) (e v) (e w)
  · exact ⟨e.injective.ne hdistinct.1, e.injective.ne hdistinct.2.1,
      e.injective.ne hdistinct.2.2⟩
  · exact hmono

theorem colorNeighborhood_mapEdgeColors {V C D : Type*}
    [Fintype V] [DecidableEq V] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D]
    (c : EdgeColoring V C) (e : C ≃ D) (q : D) (v : V) :
    colorNeighborhood (mapEdgeColors c e) q v =
      colorNeighborhood c (e.symm q) v := by
  ext w
  simp only [colorNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
    mapEdgeColors_apply]
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨hw, by simpa using congrArg e.symm h⟩
  · rintro ⟨hw, h⟩
    exact ⟨hw, by simp [h]⟩

theorem colorDegree_mapEdgeColors {V C D : Type*}
    [Fintype V] [DecidableEq V] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D]
    (c : EdgeColoring V C) (e : C ≃ D) (q : D) (v : V) :
    colorDegree (mapEdgeColors c e) q v = colorDegree c (e.symm q) v := by
  rw [colorDegree, colorDegree, colorNeighborhood_mapEdgeColors]

end R4333
