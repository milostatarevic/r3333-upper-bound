import R4333Lean.AttachingPartition
import R4333Lean.ColorRelabel

/-!
# Normalizing an ordered pair of four colours

A future finite obstruction checker should not enumerate four-colour copies
that differ only by a global palette permutation.  This file supplies the
needed kernel-visible normalization.  Two explicit swaps send any ordered
pair of distinct colours `(delta, gamma)` to the fixed pair
`((true, true), (true, false))`.

The resulting global colour relabeling preserves the no-monochromatic-
triangle condition and transports exactly the selected neighbourhoods,
degrees, intersections, and all six attaching regions.  Thus fixing these
two palette values in a canonical CNF loses no mathematical cases.
-/

namespace R4333

open Finset

/-- The fixed colour used for the selected attaching neighbourhood. -/
def normalizedDelta : FourColor := (true, true)

/-- The fixed colour used for the selected attaching edge. -/
def normalizedGamma : FourColor := (true, false)

@[simp] theorem normalizedDelta_ne_normalizedGamma :
    normalizedDelta ≠ normalizedGamma := by
  decide

@[simp] theorem normalizedGamma_ne_normalizedDelta :
    normalizedGamma ≠ normalizedDelta := by
  exact Ne.symm normalizedDelta_ne_normalizedGamma

/-- First swap `delta` to the fixed delta colour; then swap the image of
`gamma` to the fixed gamma colour.  Distinctness guarantees that the second
swap does not move the already normalized delta. -/
def fourColorPairNormalization (delta gamma : FourColor) :
    FourColor ≃ FourColor :=
  (Equiv.swap delta normalizedDelta).trans
    (Equiv.swap ((Equiv.swap delta normalizedDelta) gamma) normalizedGamma)

@[simp] theorem fourColorPairNormalization_apply_gamma
    (delta gamma : FourColor) :
    fourColorPairNormalization delta gamma gamma = normalizedGamma := by
  simp [fourColorPairNormalization]

@[simp] theorem fourColorPairNormalization_apply_delta
    (delta gamma : FourColor) (hdeltaGamma : delta ≠ gamma) :
    fourColorPairNormalization delta gamma delta = normalizedDelta := by
  let first : FourColor ≃ FourColor := Equiv.swap delta normalizedDelta
  have himages : first delta ≠ first gamma :=
    first.injective.ne hdeltaGamma
  have hfirst : normalizedDelta ≠ first gamma := by
    simpa [first] using himages
  change Equiv.swap (first gamma) normalizedGamma (first delta) =
    normalizedDelta
  rw [show first delta = normalizedDelta by simp [first]]
  exact Equiv.swap_apply_of_ne_of_ne hfirst normalizedDelta_ne_normalizedGamma

@[simp] theorem fourColorPairNormalization_symm_apply_normalizedDelta
    (delta gamma : FourColor) (hdeltaGamma : delta ≠ gamma) :
    (fourColorPairNormalization delta gamma).symm normalizedDelta = delta := by
  apply (Equiv.symm_apply_eq _).2
  exact (fourColorPairNormalization_apply_delta
    delta gamma hdeltaGamma).symm

@[simp] theorem fourColorPairNormalization_symm_apply_normalizedGamma
    (delta gamma : FourColor) :
    (fourColorPairNormalization delta gamma).symm normalizedGamma = gamma := by
  apply (Equiv.symm_apply_eq _).2
  exact (fourColorPairNormalization_apply_gamma delta gamma).symm

/-- Globally apply the explicit ordered-pair normalization to a
four-colouring. -/
def normalizeFourColorPair {V : Type*}
    (c : EdgeColoring V FourColor) (delta gamma : FourColor) :
    EdgeColoring V FourColor :=
  mapEdgeColors c (fourColorPairNormalization delta gamma)

@[simp] theorem normalizeFourColorPair_apply
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) (u v : V) :
    normalizeFourColorPair c delta gamma u v =
      fourColorPairNormalization delta gamma (c u v) :=
  rfl

/-- A global palette normalization preserves triangle-freeness. -/
theorem noMono_normalizeFourColorPair
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (normalizeFourColorPair c delta gamma) :=
  noMono_mapEdgeColors c (fourColorPairNormalization delta gamma) hc

/-- Since the palette map is bijective, normalization preserves and reflects
the no-monochromatic-triangle condition. -/
theorem noMono_normalizeFourColorPair_iff
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) :
    NoMonochromaticTriangle (normalizeFourColorPair c delta gamma) ↔
      NoMonochromaticTriangle c := by
  constructor
  · intro hnormalized x y z hdistinct hmono
    apply hnormalized x y z hdistinct
    exact ⟨congrArg (fourColorPairNormalization delta gamma) hmono.1,
      congrArg (fourColorPairNormalization delta gamma) hmono.2⟩
  · exact noMono_normalizeFourColorPair c delta gamma

/-- An edge of the selected attaching colour receives the fixed gamma
colour. -/
theorem normalizeFourColorPair_edge_eq_normalizedGamma
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) {u v : V} (hedge : c u v = gamma) :
    normalizeFourColorPair c delta gamma u v = normalizedGamma := by
  simp [normalizeFourColorPair, hedge]

/-- For distinct selected colours, normalized-delta edges are exactly the
original delta edges. -/
theorem normalizeFourColorPair_edge_eq_normalizedDelta_iff
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) (hdeltaGamma : delta ≠ gamma) (u v : V) :
    normalizeFourColorPair c delta gamma u v = normalizedDelta ↔
      c u v = delta := by
  constructor
  · intro hedge
    change fourColorPairNormalization delta gamma (c u v) =
      normalizedDelta at hedge
    apply (fourColorPairNormalization delta gamma).injective
    exact hedge.trans
      (fourColorPairNormalization_apply_delta
        delta gamma hdeltaGamma).symm
  · intro hedge
    simp [normalizeFourColorPair, hedge, hdeltaGamma]

/-- Normalized-gamma edges are exactly the original gamma edges. -/
theorem normalizeFourColorPair_edge_eq_normalizedGamma_iff
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) (u v : V) :
    normalizeFourColorPair c delta gamma u v = normalizedGamma ↔
      c u v = gamma := by
  constructor
  · intro hedge
    change fourColorPairNormalization delta gamma (c u v) =
      normalizedGamma at hedge
    apply (fourColorPairNormalization delta gamma).injective
    exact hedge.trans
      (fourColorPairNormalization_apply_gamma delta gamma).symm
  · intro hedge
    simp [normalizeFourColorPair, hedge]

/-- A selected attaching edge is therefore different from the normalized
delta colour. -/
theorem normalizeFourColorPair_attaching_edge_ne_normalizedDelta
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) {u v : V} (hedge : c u v = gamma) :
    normalizeFourColorPair c delta gamma u v ≠ normalizedDelta := by
  rw [normalizeFourColorPair_edge_eq_normalizedGamma c delta gamma hedge]
  exact normalizedGamma_ne_normalizedDelta

/-- The two selected colours and the selected attaching edge simultaneously
have the fixed values used by a normalized finite encoding. -/
theorem normalizeFourColorPair_selected_data
    {V : Type*} (c : EdgeColoring V FourColor)
    (delta gamma : FourColor) (hdeltaGamma : delta ≠ gamma)
    {u v : V} (hedge : c u v = gamma) :
    fourColorPairNormalization delta gamma delta = normalizedDelta ∧
      fourColorPairNormalization delta gamma gamma = normalizedGamma ∧
      normalizeFourColorPair c delta gamma u v = normalizedGamma ∧
      normalizeFourColorPair c delta gamma u v ≠ normalizedDelta := by
  exact ⟨fourColorPairNormalization_apply_delta
      delta gamma hdeltaGamma,
    fourColorPairNormalization_apply_gamma delta gamma,
    normalizeFourColorPair_edge_eq_normalizedGamma
      c delta gamma hedge,
    normalizeFourColorPair_attaching_edge_ne_normalizedDelta
      c delta gamma hedge⟩

/-! ## Exact transport of neighbourhood data -/

/-- Every colour neighbourhood transports to the neighbourhood of its
image under the normalization permutation. -/
theorem colorNeighborhood_normalizeFourColorPair_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma q : FourColor) (v : V) :
    colorNeighborhood (normalizeFourColorPair c delta gamma)
        (fourColorPairNormalization delta gamma q) v =
      colorNeighborhood c q v := by
  simpa [normalizeFourColorPair] using
    colorNeighborhood_mapEdgeColors c
      (fourColorPairNormalization delta gamma)
      (fourColorPairNormalization delta gamma q) v

/-- In particular, the fixed normalized-delta neighbourhood is exactly the
original selected delta neighbourhood. -/
theorem colorNeighborhood_normalizeFourColorPair_delta
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (v : V) :
    colorNeighborhood (normalizeFourColorPair c delta gamma)
        normalizedDelta v = colorNeighborhood c delta v := by
  rw [← fourColorPairNormalization_apply_delta delta gamma hdeltaGamma]
  exact colorNeighborhood_normalizeFourColorPair_image
    c delta gamma delta v

/-- The fixed normalized-gamma neighbourhood is exactly the original
selected gamma neighbourhood. -/
theorem colorNeighborhood_normalizeFourColorPair_gamma
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor) (v : V) :
    colorNeighborhood (normalizeFourColorPair c delta gamma)
        normalizedGamma v = colorNeighborhood c gamma v := by
  rw [← fourColorPairNormalization_apply_gamma delta gamma]
  exact colorNeighborhood_normalizeFourColorPair_image
    c delta gamma gamma v

/-- Exact degree transport for every colour. -/
theorem colorDegree_normalizeFourColorPair_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma q : FourColor) (v : V) :
    colorDegree (normalizeFourColorPair c delta gamma)
        (fourColorPairNormalization delta gamma q) v =
      colorDegree c q v := by
  simpa [normalizeFourColorPair] using
    colorDegree_mapEdgeColors c (fourColorPairNormalization delta gamma)
      (fourColorPairNormalization delta gamma q) v

theorem colorDegree_normalizeFourColorPair_delta
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (v : V) :
    colorDegree (normalizeFourColorPair c delta gamma) normalizedDelta v =
      colorDegree c delta v := by
  rw [← fourColorPairNormalization_apply_delta delta gamma hdeltaGamma]
  exact colorDegree_normalizeFourColorPair_image c delta gamma delta v

theorem colorDegree_normalizeFourColorPair_gamma
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor) (v : V) :
    colorDegree (normalizeFourColorPair c delta gamma) normalizedGamma v =
      colorDegree c gamma v := by
  rw [← fourColorPairNormalization_apply_gamma delta gamma]
  exact colorDegree_normalizeFourColorPair_image c delta gamma gamma v

/-- Exact transport of the selected common-neighbour intersection as a
finite set, not merely an equality of cardinalities. -/
theorem colorNeighborhood_inter_normalizeFourColorPair_delta
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (u v : V) :
    colorNeighborhood (normalizeFourColorPair c delta gamma)
        normalizedDelta u ∩
      colorNeighborhood (normalizeFourColorPair c delta gamma)
        normalizedDelta v =
      colorNeighborhood c delta u ∩ colorNeighborhood c delta v := by
  rw [colorNeighborhood_normalizeFourColorPair_delta
      c delta gamma hdeltaGamma u,
    colorNeighborhood_normalizeFourColorPair_delta
      c delta gamma hdeltaGamma v]

/-- Cardinality form of the preceding exact intersection transport. -/
theorem colorNeighborhood_inter_card_normalizeFourColorPair_delta
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (u v : V) :
    #(colorNeighborhood (normalizeFourColorPair c delta gamma)
          normalizedDelta u ∩
        colorNeighborhood (normalizeFourColorPair c delta gamma)
          normalizedDelta v) =
      #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) := by
  rw [colorNeighborhood_inter_normalizeFourColorPair_delta
    c delta gamma hdeltaGamma u v]

/-! ## Exact transport of the six attaching regions -/

/-- Every one of the six attaching-region finite sets is unchanged by the
palette normalization, after replacing `delta` by `normalizedDelta`. -/
theorem attachingRegionFinset_normalizeFourColorPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (u v : V) (r : AttachingRegion) :
    attachingRegionFinset (normalizeFourColorPair c delta gamma)
        normalizedDelta u v r =
      attachingRegionFinset c delta u v r := by
  cases r <;>
    simp [attachingRegionFinset,
      colorNeighborhood_normalizeFourColorPair_delta,
      hdeltaGamma]

/-- Identity on host vertices gives an equivalence between corresponding
normalized and original attaching-region subtypes. -/
def attachingRegionVertexNormalizationEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (u v : V) (r : AttachingRegion) :
    AttachingRegionVertex (normalizeFourColorPair c delta gamma)
        normalizedDelta u v r ≃
      AttachingRegionVertex c delta u v r where
  toFun x := ⟨x.1, by
    rw [← attachingRegionFinset_normalizeFourColorPair
      c delta gamma hdeltaGamma u v r]
    exact x.2⟩
  invFun x := ⟨x.1, by
    rw [attachingRegionFinset_normalizeFourColorPair
      c delta gamma hdeltaGamma u v r]
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

@[simp] theorem attachingRegionVertexNormalizationEquiv_apply_val
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (u v : V) (r : AttachingRegion)
    (x : AttachingRegionVertex
      (normalizeFourColorPair c delta gamma) normalizedDelta u v r) :
    (attachingRegionVertexNormalizationEquiv
      c delta gamma hdeltaGamma u v r x).1 = x.1 :=
  rfl

/-- Existing labels for every attaching region transport without making any
new finite or external choice. -/
def normalizeAttachingPartitionLabels
    {V : Type*} [Fintype V] [DecidableEq V] {du dv k : ℕ}
    (c : EdgeColoring V FourColor) (delta gamma : FourColor)
    (hdeltaGamma : delta ≠ gamma) (u v : V)
    (labels : AttachingPartitionLabels c delta u v du dv k) :
    AttachingPartitionLabels (normalizeFourColorPair c delta gamma)
      normalizedDelta u v du dv k where
  leftRoot := labels.leftRoot.trans
    (attachingRegionVertexNormalizationEquiv
      c delta gamma hdeltaGamma u v .leftRoot).symm
  rightRoot := labels.rightRoot.trans
    (attachingRegionVertexNormalizationEquiv
      c delta gamma hdeltaGamma u v .rightRoot).symm
  common := labels.common.trans
    (attachingRegionVertexNormalizationEquiv
      c delta gamma hdeltaGamma u v .common).symm
  leftOnly := labels.leftOnly.trans
    (attachingRegionVertexNormalizationEquiv
      c delta gamma hdeltaGamma u v .leftOnly).symm
  rightOnly := labels.rightOnly.trans
    (attachingRegionVertexNormalizationEquiv
      c delta gamma hdeltaGamma u v .rightOnly).symm
  outside := labels.outside.trans
    (attachingRegionVertexNormalizationEquiv
      c delta gamma hdeltaGamma u v .outside).symm

#print axioms R4333.fourColorPairNormalization_apply_delta
#print axioms R4333.noMono_normalizeFourColorPair
#print axioms R4333.noMono_normalizeFourColorPair_iff
#print axioms R4333.colorNeighborhood_normalizeFourColorPair_delta
#print axioms R4333.colorDegree_normalizeFourColorPair_delta
#print axioms R4333.colorNeighborhood_inter_normalizeFourColorPair_delta
#print axioms R4333.attachingRegionFinset_normalizeFourColorPair
#print axioms R4333.normalizeAttachingPartitionLabels

end R4333
