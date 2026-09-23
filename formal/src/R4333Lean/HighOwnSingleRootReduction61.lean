import R4333Lean.HighOwnIncidenceRootSelection61

/-!
# A high-incidence single-root reduction at order 61

The ordinary single-root front end may choose an arbitrary root carrying a
degree-sixteen colour.  The incidence argument in
`HighOwnIncidenceRootSelection61` produces a stronger root: it also receives
at least 32 oriented incidences whose endpoint has degree at least fifteen in
the colour of the joining edge.

This file constructs the existing `SingleRootStarReduction61` at a supplied
degree-sixteen root, proves that the high-incidence count is invariant under
a global palette equivalence, and combines the two facts.  The resulting
reduction therefore carries the lower bound directly in its normalized host.
-/

namespace R4333
namespace HighOwnSingleRootReduction61

open Finset
open HighOwnIncidenceRootSelection61

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-! ## Palette invariance of high own-colour incidences -/

theorem highOwnNeighborSupport_mapEdgeColors
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (e : FourColor ≃ FourColor)
    (root : V) :
    highOwnNeighborSupport (mapEdgeColors c e) root =
      highOwnNeighborSupport c root := by
  ext endpoint
  simp only [mem_highOwnNeighborSupport]
  rw [colorDegree_mapEdgeColors]
  simp

theorem highOwnNeighborCount_mapEdgeColors
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (e : FourColor ≃ FourColor)
    (root : V) :
    highOwnNeighborCount (mapEdgeColors c e) root =
      highOwnNeighborCount c root := by
  simp only [highOwnNeighborCount,
    highOwnNeighborSupport_mapEdgeColors c e root]

/-! ## The existing reduction, rooted at a supplied vertex -/

/-- Construct the checked single-root reduction at a specified root and
specified degree-sixteen colour.  This is the same construction used by
`exists_singleRootStarReduction61`, with its root choice exposed. -/
noncomputable def singleRootStarReduction61At
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (q : FourColor)
    (hq : colorDegree c q root = 16) :
    SingleRootStarReduction61 c hc := by
  classical
  let palette := singleRootPaletteEquiv c root
  let d := mapEdgeColors c palette
  have hd : NoMonochromaticTriangle d :=
    noMono_mapEdgeColors c palette hc
  let profileExists :=
    exists_unique_singleRootProfile_after_palette
      (by simp) c hc root q hq
  let profile := Classical.choose profileExists
  have hprofile :
      fourColorDegreeTuple (normalizeSingleRoot c root) root =
        singleRootProfileTuple profile :=
    (Classical.choose_spec profileExists).1
  have hsixteen : colorDegree d (palette q) root = 16 := by
    change colorDegree (mapEdgeColors c palette) (palette q) root = 16
    rw [colorDegree_mapEdgeColors]
    simpa using hq
  have hcompletion (r : FourColor)
      (hactive : colorDegree d r root = 15 ∨
        colorDegree d r root = 16) :
      SharedCriticalCompletion d hd r root :=
    Classical.choice
      (exists_sharedCriticalCompletion_of_degree d hd r root hactive)
  exact {
    root := root
    palette := palette
    profile := profile
    sixteenColor := palette q
    degreeProfile := by
      simpa [d, palette, normalizeSingleRoot] using hprofile
    sixteenDegree := hsixteen
    partition := rootColorNeighborhoodPartition d root
    activeCompletion := hcompletion
  }

@[simp] theorem singleRootStarReduction61At_root
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (q : FourColor)
    (hq : colorDegree c q root = 16) :
    (singleRootStarReduction61At c hc root q hq).root = root := by
  simp [singleRootStarReduction61At]

@[simp] theorem singleRootStarReduction61At_palette
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c)
    (root : Fin 61) (q : FourColor)
    (hq : colorDegree c q root = 16) :
    (singleRootStarReduction61At c hc root q hq).palette =
      singleRootPaletteEquiv c root := by
  simp [singleRootStarReduction61At]

/-! ## Strong normalized-root entrance -/

/-- Every hypothetical good colouring of `K61` admits a checked single-root
reduction whose normalized host receives at least 32 high own-colour
incidences at the selected root. -/
theorem exists_highOwn_singleRootStarReduction61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ data : SingleRootStarReduction61 c hc,
      32 ≤ highOwnNeighborCount
        (mapEdgeColors c data.palette) data.root := by
  obtain ⟨root, ⟨q, hq⟩, hhigh⟩ :=
    exists_degreeSixteen_root_highOwn_ge_thirtyTwo
      (by simp) c hc
  let data := singleRootStarReduction61At c hc root q hq
  refine ⟨data, ?_⟩
  rw [highOwnNeighborCount_mapEdgeColors]
  simpa [data] using hhigh

#print axioms R4333.HighOwnSingleRootReduction61.highOwnNeighborSupport_mapEdgeColors
#print axioms R4333.HighOwnSingleRootReduction61.highOwnNeighborCount_mapEdgeColors
#print axioms R4333.HighOwnSingleRootReduction61.singleRootStarReduction61At
#print axioms R4333.HighOwnSingleRootReduction61.exists_highOwn_singleRootStarReduction61

end HighOwnSingleRootReduction61
end R4333
