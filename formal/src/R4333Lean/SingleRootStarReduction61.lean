import R4333Lean.SharedCriticalCompletion
import R4333Lean.ColorRelabel
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Fin

/-!
# Single-root semantic front end at order 61

Every triangle-free four-colouring of `K61` has a colour-degree sixteen:
otherwise all four degrees at every vertex are fifteen, while any one colour
would be a 15-regular graph on 61 vertices, contrary to the handshaking
lemma.  At such a root, one genuine global palette equivalence sorts the four
degree coordinates.  The all-fifteen pattern is then unavailable, leaving
exactly four profiles.

The final structure retains the four actual colour-neighbourhood blocks,
their exact partition of the other sixty vertices, and a checked critical
template completion for every block of order fifteen or sixteen.  This file
is semantic only; it introduces no star CNF or finite-search assumption.
-/

namespace R4333

open Finset SimpleGraph

/-! ## The parity-forced degree-sixteen root -/

/-- The graph degree of one colour graph is its finite colour degree. -/
theorem colorGraph_degree_eq_colorDegree_singleRoot
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (q : C) (v : V) :
    (colorGraph c q).degree v = colorDegree c q v := by
  rw [← (colorGraph c q).card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [colorGraph, colorNeighborhood, eq_comm]

/-- A good four-colouring on 61 vertices has a vertex and colour of degree
exactly sixteen.  The only alternative allowed by the local upper bound and
the four-degree sum would make every colour graph 15-regular on an odd number
of vertices. -/
theorem exists_colorDegree_eq_sixteen_at_61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ root : V, ∃ q : FourColor, colorDegree c q root = 16 := by
  by_contra hnone
  push Not at hnone
  have hallFifteen (v : V) (q : FourColor) :
      colorDegree c q v = 15 := by
    have h00 := fourColor_colorDegree_le_sixteen c hc (false, false) v
    have h01 := fourColor_colorDegree_le_sixteen c hc (false, true) v
    have h10 := fourColor_colorDegree_le_sixteen c hc (true, false) v
    have h11 := fourColor_colorDegree_le_sixteen c hc (true, true) v
    have hn00 := hnone v (false, false)
    have hn01 := hnone v (false, true)
    have hn10 := hnone v (true, false)
    have hn11 := hnone v (true, true)
    have h00' : colorDegree c (false, false) v ≤ 15 := by omega
    have h01' : colorDegree c (false, true) v ≤ 15 := by omega
    have h10' : colorDegree c (true, false) v ≤ 15 := by omega
    have h11' : colorDegree c (true, true) v ≤ 15 := by omega
    have hsum := fourColor_degree_sum c v
    rw [hcard] at hsum
    rcases q with ⟨q₁, q₂⟩
    cases q₁ <;> cases q₂ <;> omega
  have hhandshake :=
    (colorGraph c (false, false)).sum_degrees_eq_twice_card_edges
  simp_rw [colorGraph_degree_eq_colorDegree_singleRoot,
    hallFifteen] at hhandshake
  simp [hcard] at hhandshake
  omega

/-! ## A genuine global palette sort -/

/-- Fixed natural enumeration `(00,01,10,11)` of the four colours. -/
def singleRootFourColorEquivFin4 : FourColor ≃ Fin 4 :=
  (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans
    finProdFinEquiv

@[simp] theorem singleRootFourColorEquivFin4_false_false :
    singleRootFourColorEquivFin4 (false, false) = 0 := by decide

@[simp] theorem singleRootFourColorEquivFin4_false_true :
    singleRootFourColorEquivFin4 (false, true) = 1 := by decide

@[simp] theorem singleRootFourColorEquivFin4_true_false :
    singleRootFourColorEquivFin4 (true, false) = 2 := by decide

@[simp] theorem singleRootFourColorEquivFin4_true_true :
    singleRootFourColorEquivFin4 (true, true) = 3 := by decide

@[simp] theorem singleRootFourColorEquivFin4_symm_zero :
    singleRootFourColorEquivFin4.symm 0 = (false, false) := by decide

@[simp] theorem singleRootFourColorEquivFin4_symm_one :
    singleRootFourColorEquivFin4.symm 1 = (false, true) := by decide

@[simp] theorem singleRootFourColorEquivFin4_symm_two :
    singleRootFourColorEquivFin4.symm 2 = (true, false) := by decide

@[simp] theorem singleRootFourColorEquivFin4_symm_three :
    singleRootFourColorEquivFin4.symm 3 = (true, true) := by decide

/-! The deployed Mathlib subset does not contain the built olean for
`Data.Fin.Tuple.Sort`, so its small graph-sort construction is repeated here
against the already built dependencies.  Pairing each value with its original
index makes the result a permutation even when degrees tie. -/

namespace SingleRootTupleSort

variable {n : Nat} {A : Type*} [LinearOrder A]

def graph (f : Fin n → A) : Finset (A ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)

def graphProj {f : Fin n → A} : graph f → A :=
  fun p => p.1.1

@[simp] theorem graph_card (f : Fin n → A) : (graph f).card = n := by
  rw [graph, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro i j hij
    exact congrArg (fun p => p.2) hij

def graphEquivValue (f : Fin n → A) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    simpa [graph, eq_comm, eqComm] using h

def graphEquivOrder (f : Fin n → A) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)

def sort (f : Fin n → A) : Equiv.Perm (Fin n) :=
  (graphEquivOrder f).toEquiv.trans (graphEquivValue f).symm

theorem self_comp_sort (f : Fin n → A) :
    f ∘ sort f = graphProj ∘ graphEquivOrder f := by
  show graphProj ∘
      (graphEquivValue f ∘ (graphEquivValue f).symm) ∘
        (graphEquivOrder f).toEquiv = _
  simp

theorem monotone_graphProj (f : Fin n → A) :
    Monotone (graphProj : graph f → A) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graphProj]

theorem monotone_sort (f : Fin n → A) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_graphProj f).comp (graphEquivOrder f).monotone

end SingleRootTupleSort

/-- The four root degrees in fixed natural colour order. -/
def singleRootDegreeByIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) (i : Fin 4) : Nat :=
  colorDegree c (singleRootFourColorEquivFin4.symm i) root

/-- Tie-safe permutation of the four original colours by nondecreasing root
degree. -/
noncomputable def singleRootDegreeSort
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) : Equiv.Perm (Fin 4) :=
  SingleRootTupleSort.sort (singleRootDegreeByIndex c root)

/-- Global palette equivalence sending the colour in sorted position `i` to
the fixed colour `i`. -/
noncomputable def singleRootPaletteEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) : FourColor ≃ FourColor :=
  singleRootFourColorEquivFin4.trans
    ((singleRootDegreeSort c root).symm.trans
      singleRootFourColorEquivFin4.symm)

/-- Apply the sorting palette equivalence globally to every host edge. -/
noncomputable def normalizeSingleRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) :
    EdgeColoring V FourColor :=
  mapEdgeColors c (singleRootPaletteEquiv c root)

/-- The normalization is a genuine global weak colour equivalence, with no
vertex-dependent palette choices. -/
noncomputable def normalizeSingleRootWeakColorEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) :
    WeakColorEquiv c (normalizeSingleRoot c root) where
  vertex := Equiv.refl V
  colors := singleRootPaletteEquiv c root
  map_color := by simp [normalizeSingleRoot]

theorem noMono_normalizeSingleRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (normalizeSingleRoot c root) :=
  noMono_mapEdgeColors c (singleRootPaletteEquiv c root) hc

@[simp] theorem singleRootPaletteEquiv_symm_apply_index
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) (i : Fin 4) :
    (singleRootPaletteEquiv c root).symm
        (singleRootFourColorEquivFin4.symm i) =
      singleRootFourColorEquivFin4.symm (singleRootDegreeSort c root i) := by
  simp [singleRootPaletteEquiv]

theorem colorDegree_normalizeSingleRoot_index
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) (i : Fin 4) :
    colorDegree (normalizeSingleRoot c root)
        (singleRootFourColorEquivFin4.symm i) root =
      singleRootDegreeByIndex c root (singleRootDegreeSort c root i) := by
  rw [normalizeSingleRoot, colorDegree_mapEdgeColors]
  simp [singleRootDegreeByIndex]

theorem normalizeSingleRoot_degree_monotone
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) :
    Monotone (fun i : Fin 4 =>
      colorDegree (normalizeSingleRoot c root)
        (singleRootFourColorEquivFin4.symm i) root) := by
  intro i j hij
  change colorDegree (normalizeSingleRoot c root)
      (singleRootFourColorEquivFin4.symm i) root ≤
    colorDegree (normalizeSingleRoot c root)
      (singleRootFourColorEquivFin4.symm j) root
  rw [colorDegree_normalizeSingleRoot_index,
    colorDegree_normalizeSingleRoot_index]
  exact SingleRootTupleSort.monotone_sort
    (singleRootDegreeByIndex c root) hij

theorem normalizeSingleRoot_degrees_sorted
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) :
    colorDegree (normalizeSingleRoot c root) (false, false) root ≤
      colorDegree (normalizeSingleRoot c root) (false, true) root ∧
    colorDegree (normalizeSingleRoot c root) (false, true) root ≤
      colorDegree (normalizeSingleRoot c root) (true, false) root ∧
    colorDegree (normalizeSingleRoot c root) (true, false) root ≤
      colorDegree (normalizeSingleRoot c root) (true, true) root := by
  have hmonotone := normalizeSingleRoot_degree_monotone c root
  constructor
  · simpa using hmonotone (show (0 : Fin 4) ≤ 1 by decide)
  constructor
  · simpa using hmonotone (show (1 : Fin 4) ≤ 2 by decide)
  · simpa using hmonotone (show (2 : Fin 4) ≤ 3 by decide)

/-! ## The four surviving sorted profiles -/

inductive SingleRootProfile61 where
  | twelveSixteenSixteenSixteen
  | thirteenFifteenSixteenSixteen
  | fourteenFourteenSixteenSixteen
  | fourteenFifteenFifteenSixteen
  deriving DecidableEq, Fintype, Repr

def singleRootProfileTuple : SingleRootProfile61 → FourDegreeTuple
  | .twelveSixteenSixteenSixteen => (12, 16, 16, 16)
  | .thirteenFifteenSixteenSixteen => (13, 15, 16, 16)
  | .fourteenFourteenSixteenSixteen => (14, 14, 16, 16)
  | .fourteenFifteenFifteenSixteen => (14, 15, 15, 16)

theorem singleRootProfileTuple_injective :
    Function.Injective singleRootProfileTuple := by
  intro left right h
  cases left <;> cases right <;>
    simp [singleRootProfileTuple] at h ⊢

/-- A root already known to carry a degree-sixteen colour has exactly one of
the four surviving profiles after the global palette sort. -/
theorem exists_unique_singleRootProfile_after_palette
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (root : V) (q : FourColor) (hq : colorDegree c q root = 16) :
    ∃! profile : SingleRootProfile61,
      fourColorDegreeTuple (normalizeSingleRoot c root) root =
        singleRootProfileTuple profile := by
  let d := normalizeSingleRoot c root
  have hd : NoMonochromaticTriangle d :=
    noMono_normalizeSingleRoot c root hc
  have hsorted := normalizeSingleRoot_degrees_sorted c root
  have hsum := fourColor_degree_sum d root
  rw [hcard] at hsum
  have hupper := fourColor_colorDegree_le_sixteen d hd (true, true) root
  have htransport :
      colorDegree d (singleRootPaletteEquiv c root q) root = 16 := by
    change colorDegree (normalizeSingleRoot c root)
      (singleRootPaletteEquiv c root q) root = 16
    rw [normalizeSingleRoot, colorDegree_mapEdgeColors]
    simpa using hq
  rcases degreePattern61_sorted
      (colorDegree d (false, false) root)
      (colorDegree d (false, true) root)
      (colorDegree d (true, false) root)
      (colorDegree d (true, true) root)
      hsorted.1 hsorted.2.1 hsorted.2.2 hupper (by omega) with
    hprofile | hprofile | hprofile | hprofile | hall
  · refine ⟨.twelveSixteenSixteenSixteen, ?_, ?_⟩
    · simp only [fourColorDegreeTuple, singleRootProfileTuple]
      exact Prod.ext hprofile.1 (Prod.ext hprofile.2.1
        (Prod.ext hprofile.2.2.1 hprofile.2.2.2))
    · intro other hother
      apply singleRootProfileTuple_injective
      exact hother.symm.trans (Prod.ext hprofile.1
        (Prod.ext hprofile.2.1
          (Prod.ext hprofile.2.2.1 hprofile.2.2.2)))
  · refine ⟨.thirteenFifteenSixteenSixteen, ?_, ?_⟩
    · simp only [fourColorDegreeTuple, singleRootProfileTuple]
      exact Prod.ext hprofile.1 (Prod.ext hprofile.2.1
        (Prod.ext hprofile.2.2.1 hprofile.2.2.2))
    · intro other hother
      apply singleRootProfileTuple_injective
      exact hother.symm.trans (Prod.ext hprofile.1
        (Prod.ext hprofile.2.1
          (Prod.ext hprofile.2.2.1 hprofile.2.2.2)))
  · refine ⟨.fourteenFourteenSixteenSixteen, ?_, ?_⟩
    · simp only [fourColorDegreeTuple, singleRootProfileTuple]
      exact Prod.ext hprofile.1 (Prod.ext hprofile.2.1
        (Prod.ext hprofile.2.2.1 hprofile.2.2.2))
    · intro other hother
      apply singleRootProfileTuple_injective
      exact hother.symm.trans (Prod.ext hprofile.1
        (Prod.ext hprofile.2.1
          (Prod.ext hprofile.2.2.1 hprofile.2.2.2)))
  · refine ⟨.fourteenFifteenFifteenSixteen, ?_, ?_⟩
    · simp only [fourColorDegreeTuple, singleRootProfileTuple]
      exact Prod.ext hprofile.1 (Prod.ext hprofile.2.1
        (Prod.ext hprofile.2.2.1 hprofile.2.2.2))
    · intro other hother
      apply singleRootProfileTuple_injective
      exact hother.symm.trans (Prod.ext hprofile.1
        (Prod.ext hprofile.2.1
          (Prod.ext hprofile.2.2.1 hprofile.2.2.2)))
  · have hallColors (r : FourColor) : colorDegree d r root = 15 := by
      rcases r with ⟨r₁, r₂⟩
      cases r₁ <;> cases r₂
      · exact hall.1
      · exact hall.2.1
      · exact hall.2.2.1
      · exact hall.2.2.2
    have := hallColors (singleRootPaletteEquiv c root q)
    omega

/-! ## Exact star partition and checked active blocks -/

/-- The four root colour neighbourhoods are pairwise disjoint and cover
exactly the vertices other than the root. -/
def RootColorNeighborhoodPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) : Prop :=
  ((Finset.univ : Finset FourColor).biUnion fun q =>
      colorNeighborhood c q root) =
      (Finset.univ : Finset V).erase root ∧
    ∀ q r : FourColor, q ≠ r →
      Disjoint (colorNeighborhood c q root)
        (colorNeighborhood c r root)

theorem rootColorNeighborhoodPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) :
    RootColorNeighborhoodPartition c root := by
  classical
  constructor
  · ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      mem_colorNeighborhood, Finset.mem_erase]
    constructor
    · rintro ⟨q, hv, _⟩
      exact ⟨hv, trivial⟩
    · rintro ⟨hv, _⟩
      exact ⟨c root v, hv, rfl⟩
  · intro q r hqr
    rw [Finset.disjoint_left]
    intro v hvq hvr
    have hq := (mem_colorNeighborhood c q root v).mp hvq
    have hr := (mem_colorNeighborhood c r root v).mp hvr
    exact hqr (hq.2.symm.trans hr.2)

/-- On the concrete host, the union in the preceding partition has exactly
sixty vertices. -/
theorem rootColorNeighborhoodUnion_card_eq_sixty
    (c : EdgeColoring (Fin 61) FourColor) (root : Fin 61) :
    #((Finset.univ : Finset FourColor).biUnion fun q =>
      colorNeighborhood c q root) = 60 := by
  rw [(rootColorNeighborhoodPartition c root).1]
  simp

/-- Complete semantic single-root data retained for the eventual star layer.
Every active block stores an actual `SharedCriticalCompletion`, whose `kind`
field is a checked `CriticalTemplateKind` and whose weak equivalence covers
the whole neighbourhood. -/
structure SingleRootStarReduction61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) where
  root : Fin 61
  palette : FourColor ≃ FourColor
  profile : SingleRootProfile61
  sixteenColor : FourColor
  degreeProfile :
    fourColorDegreeTuple (mapEdgeColors c palette) root =
      singleRootProfileTuple profile
  sixteenDegree :
    colorDegree (mapEdgeColors c palette) sixteenColor root = 16
  partition : RootColorNeighborhoodPartition
    (mapEdgeColors c palette) root
  activeCompletion : ∀ q : FourColor,
    colorDegree (mapEdgeColors c palette) q root = 15 ∨
      colorDegree (mapEdgeColors c palette) q root = 16 →
    SharedCriticalCompletion
      (mapEdgeColors c palette)
      (noMono_mapEdgeColors c palette hc) q root

namespace SingleRootStarReduction61

/-- The stored palette is itself the colour component of a global weak
equivalence; the vertex component is the identity. -/
def globalWeakColorEquiv
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    WeakColorEquiv c (mapEdgeColors c data.palette) where
  vertex := Equiv.refl (Fin 61)
  colors := data.palette
  map_color := by simp

/-- Extract the checked kind attached to any active block. -/
def activeKind
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (q : FourColor)
    (hactive : colorDegree (mapEdgeColors c data.palette) q data.root = 15 ∨
      colorDegree (mapEdgeColors c data.palette) q data.root = 16) :
    CriticalTemplateKind :=
  (data.activeCompletion q hactive).kind

theorem activeDegree_eq_templateOrder
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (q : FourColor)
    (hactive : colorDegree (mapEdgeColors c data.palette) q data.root = 15 ∨
      colorDegree (mapEdgeColors c data.palette) q data.root = 16) :
    colorDegree (mapEdgeColors c data.palette) q data.root =
      criticalTemplateOrder (data.activeKind q hactive) :=
  (data.activeCompletion q hactive).degree_eq_order

/-- The checked weak equivalence from the entire active neighbourhood to its
stored critical template. -/
def activeWeakColorEquiv
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (q : FourColor)
    (hactive : colorDegree (mapEdgeColors c data.palette) q data.root = 15 ∨
      colorDegree (mapEdgeColors c data.palette) q data.root = 16) :
    WeakColorEquiv
      (neighborhoodThreeColoring
        (mapEdgeColors c data.palette)
        (noMono_mapEdgeColors c data.palette hc) q data.root)
      (criticalTemplateColoring (data.activeKind q hactive)) :=
  (data.activeCompletion q hactive).weakEquiv

end SingleRootStarReduction61

/-- Unconditional checked single-root front end for every hypothetical good
four-colouring of `K61`. -/
theorem exists_singleRootStarReduction61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) :
    Nonempty (SingleRootStarReduction61 c hc) := by
  classical
  obtain ⟨root, q, hq⟩ :=
    exists_colorDegree_eq_sixteen_at_61 (by simp) c hc
  let palette := singleRootPaletteEquiv c root
  let d := mapEdgeColors c palette
  have hd : NoMonochromaticTriangle d :=
    noMono_mapEdgeColors c palette hc
  obtain ⟨profile, hprofile, hunique⟩ :=
    exists_unique_singleRootProfile_after_palette
      (by simp) c hc root q hq
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
  exact ⟨{
    root := root
    palette := palette
    profile := profile
    sixteenColor := palette q
    degreeProfile := by
      simpa [d, palette, normalizeSingleRoot] using hprofile
    sixteenDegree := hsixteen
    partition := rootColorNeighborhoodPartition d root
    activeCompletion := hcompletion
  }⟩

#print axioms R4333.exists_colorDegree_eq_sixteen_at_61
#print axioms R4333.singleRootProfileTuple_injective
#print axioms R4333.exists_unique_singleRootProfile_after_palette
#print axioms R4333.rootColorNeighborhoodPartition
#print axioms R4333.rootColorNeighborhoodUnion_card_eq_sixty
#print axioms R4333.SingleRootStarReduction61.activeDegree_eq_templateOrder
#print axioms R4333.exists_singleRootStarReduction61

end R4333
