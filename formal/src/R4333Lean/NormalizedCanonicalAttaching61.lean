import R4333Lean.FourColorPairNormalization
import R4333Lean.CanonicalAttachingHost
import R4333Lean.CriticalCatalogues

/-!
# A normalized canonical attaching package at order 61

This file joins four already checked reductions without hiding any change of
labels.  Starting from a good four-colouring of `K61`, it:

1. selects the checked attaching configuration;
2. sends its neighbourhood colour and edge colour to `normalizedDelta` and
   `normalizedGamma` by the explicit two-swap palette equivalence;
3. rebuilds the critical finite-obstruction interface at the *same roots*;
4. transports the original six region labels exactly; and
5. pulls one global `Fin 35` degree-row selection through the canonical host
   equivalence, so the global and canonical selectors are definitionally
   related rather than independently chosen.

The critical overlap itself is rebuilt from the checked K15/K16 catalogues.
This is intentional: an old weak colour equivalence contains a palette map
for the old four-colour labels, while the catalogue theorem can soundly
produce the required normalized witness directly.
-/

namespace R4333

open Finset

/-! ## Degree rows under a vertex equivalence -/

/-- Pulling a colouring back along a vertex equivalence preserves every
colour degree exactly. -/
theorem colorDegree_relabelVertices
    {V W C : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [DecidableEq C]
    (c : EdgeColoring V C) (e : W ≃ V) (q : C) (w : W) :
    colorDegree (relabelVertices c e) q w = colorDegree c q (e w) := by
  change #(colorNeighborhood (relabelVertices c e) q w) =
    #(colorNeighborhood c q (e w))
  exact Finset.card_equiv e fun x ↦ by
    simp only [mem_colorNeighborhood, relabelVertices_apply]
    constructor
    · rintro ⟨hxw, hcolor⟩
      exact ⟨e.injective.ne hxw, hcolor⟩
    · rintro ⟨hexw, hcolor⟩
      exact ⟨fun hxw ↦ hexw (congrArg e hxw), hcolor⟩

/-- Hence the fixed-order four-degree tuple pulls back pointwise. -/
theorem fourColorDegreeTuple_relabelVertices
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (c : EdgeColoring V FourColor) (e : W ≃ V) (w : W) :
    fourColorDegreeTuple (relabelVertices c e) w =
      fourColorDegreeTuple c (e w) := by
  simp [fourColorDegreeTuple, colorDegree_relabelVertices]

namespace DegreeTargetSelection61

/-- Pull one global row selection through a vertex equivalence.  The
canonical selector below is constructed with this operation, not selected a
second time. -/
def pullback
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {c : EdgeColoring V FourColor}
    (selection : DegreeTargetSelection61 c) (e : W ≃ V) :
    DegreeTargetSelection61 (relabelVertices c e) where
  index w := selection.index (e w)
  index_eq w := (selection.index_eq (e w)).trans
    (fourColorDegreeTuple_relabelVertices c e w).symm

@[simp] theorem pullback_index
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {c : EdgeColoring V FourColor}
    (selection : DegreeTargetSelection61 c) (e : W ≃ V) (w : W) :
    (selection.pullback e).index w = selection.index (e w) :=
  rfl

end DegreeTargetSelection61

/-! ## The same attaching pair after palette normalization -/

/-- A catalogued attaching configuration survives the explicit palette
normalization at the same ordered pair of roots.  Only the two catalogue
witnesses are rebuilt, from their transported 15/16 degree bounds and the
fully checked catalogues. -/
theorem cataloguedAttachingConfiguration_normalize
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (u v : V)
    (hconfig : CataloguedAttachingConfiguration c hc delta u v) :
    CataloguedAttachingConfiguration
      (normalizeFourColorPair c delta (c u v))
      (noMono_normalizeFourColorPair c delta (c u v) hc)
      normalizedDelta u v := by
  obtain ⟨huv, hedge, hgamma, huLower, huUpper,
      hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
      _huCatalogue, _hvCatalogue⟩ := hconfig
  let normalized := normalizeFourColorPair c delta (c u v)
  let hnormalized : NoMonochromaticTriangle normalized :=
    noMono_normalizeFourColorPair c delta (c u v) hc
  change CataloguedAttachingConfiguration
    normalized hnormalized normalizedDelta u v
  have hdeltaGamma : delta ≠ c u v := Ne.symm hedge
  have hedgeNormalized : normalized u v = normalizedGamma := by
    simp [normalized]
  have hgammaDegree :
      colorDegree normalized normalizedGamma u =
        colorDegree c (c u v) u := by
    simpa [normalized] using
      colorDegree_normalizeFourColorPair_gamma c delta (c u v) u
  have huDegree :
      colorDegree normalized normalizedDelta u =
        colorDegree c delta u := by
    simpa [normalized] using
      colorDegree_normalizeFourColorPair_delta
        c delta (c u v) hdeltaGamma u
  have hvDegree :
      colorDegree normalized normalizedDelta v =
        colorDegree c delta v := by
    simpa [normalized] using
      colorDegree_normalizeFourColorPair_delta
        c delta (c u v) hdeltaGamma v
  have hintersection :
      #(colorNeighborhood normalized normalizedDelta u ∩
          colorNeighborhood normalized normalizedDelta v) =
        #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) := by
    simpa [normalized] using
      colorNeighborhood_inter_card_normalizeFourColorPair_delta
        c delta (c u v) hdeltaGamma u v
  have hgammaNormalized :
      14 ≤ colorDegree normalized (normalized u v) u := by
    rw [hedgeNormalized, hgammaDegree]
    exact hgamma
  have huLowerNormalized :
      15 ≤ colorDegree normalized normalizedDelta u := by
    rw [huDegree]
    exact huLower
  have huUpperNormalized :
      colorDegree normalized normalizedDelta u ≤ 16 := by
    rw [huDegree]
    exact huUpper
  have hvLowerNormalized :
      15 ≤ colorDegree normalized normalizedDelta v := by
    rw [hvDegree]
    exact hvLower
  have hvUpperNormalized :
      colorDegree normalized normalizedDelta v ≤ 16 := by
    rw [hvDegree]
    exact hvUpper
  have huCatalogueNormalized := criticalNeighborhoodWitness_of_bounds
    normalized hnormalized normalizedDelta u
      huLowerNormalized huUpperNormalized
      k15CriticalCatalogue_complete k16CriticalCatalogue_complete
  have hvCatalogueNormalized := criticalNeighborhoodWitness_of_bounds
    normalized hnormalized normalizedDelta v
      hvLowerNormalized hvUpperNormalized
      k15CriticalCatalogue_complete k16CriticalCatalogue_complete
  refine ⟨huv, ?_, hgammaNormalized,
    huLowerNormalized, huUpperNormalized,
    hvLowerNormalized, hvUpperNormalized, ?_, ?_, ?_, ?_,
    huCatalogueNormalized, hvCatalogueNormalized⟩
  · rw [hedgeNormalized]
    exact normalizedGamma_ne_normalizedDelta
  · rw [hintersection]
    exact hkLower
  · rw [hintersection]
    exact hkUpper
  · rw [hedgeNormalized, hgammaDegree, hintersection, hvDegree]
    exact hsharp
  · rw [hintersection, hvDegree]
    exact hplus

/-! ## Exact source-to-normalized interface bridge -/

namespace FiniteObstructionInterface

/-- The normalized colouring determined by the source interface's selected
delta and actual attaching-edge colour. -/
def normalizedColoring
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (_interface : FiniteObstructionInterface c hc delta u v) :
    EdgeColoring V FourColor :=
  normalizeFourColorPair c delta (c u v)

/-- The normalized colouring is still triangle-free. -/
theorem normalizedNoMono
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    NoMonochromaticTriangle interface.normalizedColoring :=
  noMono_normalizeFourColorPair c delta (c u v) hc

/-- The source attaching condition supplies the distinctness required by
the ordered-pair palette normalization. -/
theorem delta_ne_attachingColor
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    delta ≠ c u v :=
  Ne.symm interface.attaching.2.1

/-- The original attaching configuration transported to the normalized
colouring, with the same roots. -/
theorem normalizedAttaching
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    CataloguedAttachingConfiguration interface.normalizedColoring
      interface.normalizedNoMono normalizedDelta u v := by
  simpa [normalizedColoring, normalizedNoMono] using
    cataloguedAttachingConfiguration_normalize
      c hc delta u v interface.attaching

/-- The selected root edge has the fixed normalized gamma colour. -/
theorem normalized_edge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    interface.normalizedColoring u v = normalizedGamma := by
  exact normalizeFourColorPair_edge_eq_normalizedGamma
    c delta (c u v) rfl

/-- Every normalized attaching region is exactly the corresponding source
region as a finite set of host vertices. -/
theorem normalizedRegion_eq_source
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v)
    (r : AttachingRegion) :
    attachingRegionFinset interface.normalizedColoring
        normalizedDelta u v r =
      attachingRegionFinset c delta u v r := by
  exact attachingRegionFinset_normalizeFourColorPair
    c delta (c u v) interface.delta_ne_attachingColor u v r

/-- Transport the interface's exact six label equivalences, then rewrite
their three size parameters to the values computed in the normalized
colouring. -/
def normalizedPartitionLabels
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    AttachingPartitionLabels interface.normalizedColoring normalizedDelta u v
      (colorDegree interface.normalizedColoring normalizedDelta u)
      (colorDegree interface.normalizedColoring normalizedDelta v)
      #(colorNeighborhood interface.normalizedColoring normalizedDelta u ∩
        colorNeighborhood interface.normalizedColoring normalizedDelta v) := by
  change AttachingPartitionLabels
    (normalizeFourColorPair c delta (c u v)) normalizedDelta u v
      (colorDegree (normalizeFourColorPair c delta (c u v))
        normalizedDelta u)
      (colorDegree (normalizeFourColorPair c delta (c u v))
        normalizedDelta v)
      #(colorNeighborhood (normalizeFourColorPair c delta (c u v))
          normalizedDelta u ∩
        colorNeighborhood (normalizeFourColorPair c delta (c u v))
          normalizedDelta v)
  rw [colorDegree_normalizeFourColorPair_delta
      c delta (c u v) interface.delta_ne_attachingColor u,
    colorDegree_normalizeFourColorPair_delta
      c delta (c u v) interface.delta_ne_attachingColor v,
    colorNeighborhood_inter_card_normalizeFourColorPair_delta
      c delta (c u v) interface.delta_ne_attachingColor u v]
  exact normalizeAttachingPartitionLabels c delta (c u v)
    interface.delta_ne_attachingColor u v interface.partitionLabels

end FiniteObstructionInterface

/-- A normalized finite interface tied explicitly to the source labels and
to one global degree-row selection. -/
structure NormalizedFiniteObstructionBridge
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (source : FiniteObstructionInterface c hc delta u v) where
  globalDegreeTargets : DegreeTargetSelection61 source.normalizedColoring
  interface : FiniteObstructionInterface source.normalizedColoring
    source.normalizedNoMono normalizedDelta u v
  partitionLabels_eq :
    interface.partitionLabels = source.normalizedPartitionLabels
  leftDegreeTarget_eq_global :
    interface.leftDegreeTarget = globalDegreeTargets.index u
  rightDegreeTarget_eq_global :
    interface.rightDegreeTarget = globalDegreeTargets.index v

namespace NormalizedFiniteObstructionBridge

/-- The canonical equivalence sends a region/index pair to the exact host
vertex selected by that region's retained label equivalence. -/
@[simp] theorem canonicalEquiv_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source)
    (r : AttachingRegion)
    (i : Fin (attachingRegionSize
      (colorDegree source.normalizedColoring normalizedDelta u)
      (colorDegree source.normalizedColoring normalizedDelta v)
      #(colorNeighborhood source.normalizedColoring normalizedDelta u ∩
        colorNeighborhood source.normalizedColoring normalizedDelta v) r)) :
    bridge.interface.canonicalEquiv ⟨r, i⟩ =
      (bridge.interface.partitionLabels.regionEquiv r i).1 :=
  rfl

/-- The canonical left-root label is the original selected left endpoint. -/
@[simp] theorem canonicalEquiv_leftRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source) (i : Fin 1) :
    bridge.interface.canonicalEquiv ⟨.leftRoot, i⟩ = u := by
  change (bridge.interface.partitionLabels.leftRoot i).1 = u
  exact (mem_attachingRegion_leftRoot
    source.normalizedColoring normalizedDelta u v _).mp
      (bridge.interface.partitionLabels.leftRoot i).2

/-- The canonical right-root label is the original selected right endpoint. -/
@[simp] theorem canonicalEquiv_rightRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source) (i : Fin 1) :
    bridge.interface.canonicalEquiv ⟨.rightRoot, i⟩ = v := by
  change (bridge.interface.partitionLabels.rightRoot i).1 = v
  exact (mem_attachingRegion_rightRoot
    source.normalizedColoring normalizedDelta u v _).mp
      (bridge.interface.partitionLabels.rightRoot i).2

/-- Pull the bridge's one global degree-row selection through the exact
canonical equivalence carried by its normalized interface. -/
noncomputable def canonicalDegreeTargets
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source) :
    DegreeTargetSelection61 bridge.interface.canonicalColoring :=
  bridge.globalDegreeTargets.pullback bridge.interface.canonicalEquiv

@[simp] theorem canonicalDegreeTargets_index
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source)
    (x : CanonicalAttachingVertex
      (colorDegree source.normalizedColoring normalizedDelta u)
      (colorDegree source.normalizedColoring normalizedDelta v)
      #(colorNeighborhood source.normalizedColoring normalizedDelta u ∩
        colorNeighborhood source.normalizedColoring normalizedDelta v)) :
    bridge.canonicalDegreeTargets.index x =
      bridge.globalDegreeTargets.index (bridge.interface.canonicalEquiv x) :=
  rfl

/-- The canonical colouring is literally the normalized host colouring
pulled back along the interface's six-region equivalence. -/
@[simp] theorem canonicalColoring_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source)
    (x y : CanonicalAttachingVertex
      (colorDegree source.normalizedColoring normalizedDelta u)
      (colorDegree source.normalizedColoring normalizedDelta v)
      #(colorNeighborhood source.normalizedColoring normalizedDelta u ∩
        colorNeighborhood source.normalizedColoring normalizedDelta v)) :
    bridge.interface.canonicalColoring x y =
      source.normalizedColoring
        (bridge.interface.canonicalEquiv x)
        (bridge.interface.canonicalEquiv y) :=
  rfl

/-- In canonical coordinates the selected root edge has exactly the fixed
normalized gamma colour. -/
@[simp] theorem canonical_root_edge_eq_normalizedGamma
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source)
    (i j : Fin 1) :
    bridge.interface.canonicalColoring
        ⟨AttachingRegion.leftRoot, i⟩
        ⟨AttachingRegion.rightRoot, j⟩ = normalizedGamma := by
  rw [bridge.canonicalColoring_apply,
    bridge.canonicalEquiv_leftRoot,
    bridge.canonicalEquiv_rightRoot]
  exact source.normalized_edge_eq

/-- The canonical left-root row is the normalized interface's left row and
the global row at the actual endpoint. -/
theorem canonicalDegreeTargets_leftRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source) (i : Fin 1) :
    bridge.canonicalDegreeTargets.index
        ⟨AttachingRegion.leftRoot, i⟩ =
      bridge.interface.leftDegreeTarget := by
  rw [bridge.canonicalDegreeTargets_index,
    bridge.canonicalEquiv_leftRoot,
    bridge.leftDegreeTarget_eq_global]

/-- The analogous exact relation for the canonical right root. -/
theorem canonicalDegreeTargets_rightRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    {source : FiniteObstructionInterface c hc delta u v}
    (bridge : NormalizedFiniteObstructionBridge source) (i : Fin 1) :
    bridge.canonicalDegreeTargets.index
        ⟨AttachingRegion.rightRoot, i⟩ =
      bridge.interface.rightDegreeTarget := by
  rw [bridge.canonicalDegreeTargets_index,
    bridge.canonicalEquiv_rightRoot,
    bridge.rightDegreeTarget_eq_global]

end NormalizedFiniteObstructionBridge

/-- Rebuild the normalized critical interface while retaining the exact
transported partition labels and choosing its two root rows from the same
global degree selection. -/
theorem exists_normalizedFiniteObstructionBridge
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (source : FiniteObstructionInterface c hc delta u v) :
    Nonempty (NormalizedFiniteObstructionBridge source) := by
  obtain ⟨globalTargets⟩ := exists_degreeTargetSelection61
    source.hostCard source.normalizedColoring source.normalizedNoMono
  have hconfig : CataloguedAttachingConfiguration source.normalizedColoring
      source.normalizedNoMono normalizedDelta u v :=
    source.normalizedAttaching
  obtain ⟨huv, hedge, hgamma, huLower, huUpper,
      hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
      huCatalogue, hvCatalogue⟩ := hconfig
  have hconfig' : CataloguedAttachingConfiguration source.normalizedColoring
      source.normalizedNoMono normalizedDelta u v :=
    ⟨huv, hedge, hgamma, huLower, huUpper,
      hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
      huCatalogue, hvCatalogue⟩
  let k := #(colorNeighborhood source.normalizedColoring normalizedDelta u ∩
    colorNeighborhood source.normalizedColoring normalizedDelta v)
  obtain ⟨criticalOverlap, huOrder, hvOrder⟩ :=
    exists_labeledCriticalTemplateOverlap_of_witnesses
      (k := k) source.normalizedColoring source.normalizedNoMono
      normalizedDelta u v huCatalogue hvCatalogue (by rfl)
  have hdegreeSum :
      colorDegree source.normalizedColoring normalizedDelta u +
        colorDegree source.normalizedColoring normalizedDelta v ≤ 59 := by
    omega
  have hregionCards : ExactAttachingRegionCards
      source.normalizedColoring normalizedDelta u v := by
    exact attachingRegion_cards source.hostCard source.normalizedColoring
      normalizedDelta u v huv hedge (by rfl) (by rfl) (by rfl) hdegreeSum
  let normalizedInterface : FiniteObstructionInterface
      source.normalizedColoring source.normalizedNoMono
      normalizedDelta u v := {
    hostCard := source.hostCard
    attaching := hconfig'
    leftDegreeTarget := globalTargets.index u
    leftDegreeTarget_eq := globalTargets.index_eq u
    rightDegreeTarget := globalTargets.index v
    rightDegreeTarget_eq := globalTargets.index_eq v
    partitionLabels := source.normalizedPartitionLabels
    partitionCards := hregionCards
    criticalOverlap := criticalOverlap
    leftTemplateOrder := huOrder
    rightTemplateOrder := hvOrder
    overlapCompatible := by
      intro i j hij
      exact criticalOverlap.compatible i j hij
  }
  exact ⟨{
    globalDegreeTargets := globalTargets
    interface := normalizedInterface
    partitionLabels_eq := by rfl
    leftDegreeTarget_eq_global := by rfl
    rightDegreeTarget_eq_global := by rfl
  }⟩

/-! ## The complete order-61 package -/

/-- All normalized and canonical data selected from one hypothetical good
four-colouring of `K61`. -/
structure NormalizedCanonicalAttaching61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) where
  delta : FourColor
  u : Fin 61
  v : Fin 61
  source : FiniteObstructionInterface c hc delta u v
  bridge : NormalizedFiniteObstructionBridge source

/-- Every good four-colouring of `K61` has the normalized canonical package.
This is still an extraction theorem; it asserts no final finite
contradiction. -/
theorem exists_normalizedCanonicalAttaching61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) :
    Nonempty (NormalizedCanonicalAttaching61 c hc) := by
  obtain ⟨delta, u, v, ⟨source⟩⟩ :=
    exists_finiteObstructionInterface61_checked c hc
  obtain ⟨bridge⟩ := exists_normalizedFiniteObstructionBridge source
  exact ⟨{
    delta := delta
    u := u
    v := v
    source := source
    bridge := bridge
  }⟩

namespace NormalizedCanonicalAttaching61

/-- The package's canonical degree rows are exactly its global rows evaluated
at the host image of each canonical six-region vertex. -/
noncomputable def canonicalDegreeTargets
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (package : NormalizedCanonicalAttaching61 c hc) :
    DegreeTargetSelection61 package.bridge.interface.canonicalColoring :=
  package.bridge.canonicalDegreeTargets

/-- The normalized root edge has the fixed second distinguished colour. -/
theorem normalized_edge_eq
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (package : NormalizedCanonicalAttaching61 c hc) :
    package.source.normalizedColoring package.u package.v =
      normalizedGamma :=
  package.source.normalized_edge_eq

/-- The package records exact transport, rather than an unrelated fresh
choice, of all six source partition label equivalences. -/
theorem partitionLabels_eq_transported
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (package : NormalizedCanonicalAttaching61 c hc) :
    package.bridge.interface.partitionLabels =
      package.source.normalizedPartitionLabels :=
  package.bridge.partitionLabels_eq

#print axioms R4333.colorDegree_relabelVertices
#print axioms R4333.cataloguedAttachingConfiguration_normalize
#print axioms R4333.FiniteObstructionInterface.normalizedPartitionLabels
#print axioms R4333.exists_normalizedFiniteObstructionBridge
#print axioms R4333.exists_normalizedCanonicalAttaching61
#print axioms R4333.NormalizedCanonicalAttaching61.canonicalDegreeTargets

end NormalizedCanonicalAttaching61

end R4333
