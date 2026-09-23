import R4333Lean.CriticalCatalogues
import R4333Lean.FiniteObstructionInterface

/-!
# Shared critical completions for every active neighbourhood

Every colour coordinate of degree fifteen or sixteen has a full critical
K15/K16 template, not merely a private completion of some selected subset.
The vertex equivalence below labels *all* actual neighbours of the root, so
the same object also controls neighbours that happen to lie in an attaching
partition's outside region.
-/

namespace R4333

/-- A checked critical template for one complete monochromatic
neighbourhood. -/
structure SharedCriticalCompletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (q : FourColor) (root : V) where
  kind : CriticalTemplateKind
  degree_eq_order : colorDegree c q root = criticalTemplateOrder kind
  weakEquiv : WeakColorEquiv
    (neighborhoodThreeColoring c hc q root)
    (criticalTemplateColoring kind)

namespace SharedCriticalCompletion

/-- A bijective assignment from every actual `q`-neighbour to a vertex of
the selected critical template. -/
def neighborEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root) :
    NeighborhoodVertex c q root ≃ CriticalTemplateVertex completion.kind :=
  completion.weakEquiv.vertex

/-- The palette map from the three actual non-`q` colours to the template's
three labels. -/
def paletteEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root) :
    NeighborhoodColor q ≃ ThreeColor :=
  completion.weakEquiv.colors

/-- Apply the shared template assignment directly to a host vertex together
with evidence that it is a `q`-neighbour.  No attaching-region condition is
present. -/
def mapNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root)
    (x : V) (hx : x ∈ colorNeighborhood c q root) :
    CriticalTemplateVertex completion.kind :=
  completion.neighborEquiv ⟨x, hx⟩

/-- Different actual neighbours receive different template vertices. -/
theorem mapNeighbor_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root)
    {x y : V} (hx : x ∈ colorNeighborhood c q root)
    (hy : y ∈ colorNeighborhood c q root)
    (hmap : completion.mapNeighbor x hx = completion.mapNeighbor y hy) :
    x = y := by
  have hsubtype :
      (⟨x, hx⟩ : NeighborhoodVertex c q root) =
        ⟨y, hy⟩ := completion.neighborEquiv.injective hmap
  exact congrArg Subtype.val hsubtype

/-- Every template vertex has one unique actual-neighbour preimage. -/
theorem existsUnique_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root)
    (i : CriticalTemplateVertex completion.kind) :
    ∃! x : NeighborhoodVertex c q root, completion.neighborEquiv x = i := by
  refine ⟨completion.neighborEquiv.symm i,
    completion.neighborEquiv.apply_symm_apply i, ?_⟩
  intro x hx
  apply completion.neighborEquiv.injective
  simp [hx]

/-- Exact pairwise induced-colour compatibility for the whole
neighbourhood. -/
theorem pairwise_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root)
    (x y : NeighborhoodVertex c q root) (hxy : x ≠ y) :
    completion.paletteEquiv
        (neighborhoodThreeColoring c hc q root x y) =
      criticalTemplateColoring completion.kind
        (completion.neighborEquiv x) (completion.neighborEquiv y) :=
  completion.weakEquiv.map_color x y hxy

/-- Undoing the palette labels on a template edge recovers the original
four-colour of the corresponding host edge. -/
theorem original_color_of_template_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root)
    (x y : NeighborhoodVertex c q root) (hxy : x ≠ y) :
    (((completion.paletteEquiv.symm
        (criticalTemplateColoring completion.kind
          (completion.neighborEquiv x) (completion.neighborEquiv y)) :
      NeighborhoodColor q)) : FourColor) = c x.1 y.1 := by
  have hcompat := completion.pairwise_compatible x y hxy
  have hinverse :
      completion.paletteEquiv.symm
          (criticalTemplateColoring completion.kind
            (completion.neighborEquiv x) (completion.neighborEquiv y)) =
        neighborhoodThreeColoring c hc q root x y := by
    simpa using congrArg completion.paletteEquiv.symm hcompat |>.symm
  exact (congrArg Subtype.val hinverse).trans
    (neighborhoodThreeColoring_coe_apply_of_ne c hc q root x y hxy)

end SharedCriticalCompletion

/-- The unconditional checked catalogues select a shared critical completion
for every degree-15 or degree-16 colour neighbourhood. -/
theorem exists_sharedCriticalCompletion_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (q : FourColor) (root : V)
    (hdegree : colorDegree c q root = 15 ∨
      colorDegree c q root = 16) :
    Nonempty (SharedCriticalCompletion c hc q root) := by
  have hlower : 15 ≤ colorDegree c q root := by omega
  have hupper : colorDegree c q root ≤ 16 := by omega
  have hwitness := criticalNeighborhoodWitness_of_bounds c hc q root
    hlower hupper k15CriticalCatalogue_complete k16CriticalCatalogue_complete
  obtain ⟨kind, horder, ⟨weakEquiv⟩⟩ :=
    (criticalNeighborhoodWitness_iff_exists_kind c hc q root).mp hwitness
  exact ⟨{
    kind := kind
    degree_eq_order := horder
    weakEquiv := weakEquiv
  }⟩

/-- Read the coordinate of a four-degree tuple selected by a concrete
four-colour. -/
def fourDegreeTupleAtColor (target : FourDegreeTuple) :
    FourColor → ℕ
  | (false, false) => target.1
  | (false, true) => target.2.1
  | (true, false) => target.2.2.1
  | (true, true) => target.2.2.2

@[simp] theorem fourDegreeTupleAtColor_fourColorDegreeTuple
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) (q : FourColor) :
    fourDegreeTupleAtColor (fourColorDegreeTuple c root) q =
      colorDegree c q root := by
  rcases q with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- Every active (15/16) coordinate of a selected 35-row degree target has
one shared critical completion. -/
theorem exists_sharedCriticalCompletion_of_degreeTargetAt61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (targetIndex : Fin 35)
    (htarget : degreeTargetAt61 targetIndex = fourColorDegreeTuple c root)
    (q : FourColor)
    (hactive : fourDegreeTupleAtColor (degreeTargetAt61 targetIndex) q = 15 ∨
      fourDegreeTupleAtColor (degreeTargetAt61 targetIndex) q = 16) :
    Nonempty (SharedCriticalCompletion c hc q root) := by
  apply exists_sharedCriticalCompletion_of_degree c hc q root
  rw [htarget, fourDegreeTupleAtColor_fourColorDegreeTuple] at hactive
  exact hactive

#print axioms R4333.SharedCriticalCompletion.pairwise_compatible
#print axioms R4333.SharedCriticalCompletion.original_color_of_template_edge
#print axioms R4333.exists_sharedCriticalCompletion_of_degree
#print axioms R4333.exists_sharedCriticalCompletion_of_degreeTargetAt61

end R4333
