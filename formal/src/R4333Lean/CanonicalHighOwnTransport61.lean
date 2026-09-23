import R4333Lean.HighOwnSingleRootReduction61
import R4333Lean.CanonicalStarOwnColorDegree

/-!
# Transporting high own-colour incidences to canonical star coordinates

The high-incidence root theorem is stated on the normalized `K61` host,
whereas all profile CNFs use the canonical `Fin 60` non-root star.  This file
proves the exact bridge between those coordinate systems.

The reusable deletion lemma says that pulling a colouring back through an
equivalence onto the vertices other than a root removes exactly one edge
from the degree in the root-edge colour.  The canonical host relabeling is
such an equivalence.  Consequently an endpoint of full own-colour degree at
least fifteen corresponds exactly to a canonical vertex of non-root
own-block degree at least fourteen, and their finite supports have equal
cardinality.
-/

namespace R4333
namespace CanonicalHighOwnTransport61

open Finset
open SingleRootStarCNF
open SingleRootStarWitness61
open CanonicalStarOwnColorDegree
open HighOwnIncidenceRootSelection61

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-! ## Generic deletion of one root -/

/-- Pulling a colouring back through an equivalence onto all vertices except
`root` subtracts exactly the root edge from the degree in its colour. -/
theorem colorDegree_pullback_nonRoot_add_one
    {V W C : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [DecidableEq C]
    (c : EdgeColoring V C) (root : V)
    (e : W ≃ {v : V // v ≠ root})
    (q : C) (x : W)
    (hrootColor : c root (e x).val = q) :
    colorDegree
        (pullbackColoring c (fun y => (e y).val)) q x + 1 =
      colorDegree c q (e x).val := by
  let f : W → V := fun y => (e y).val
  have hf : Function.Injective f := by
    intro a b hab
    apply e.injective
    exact Subtype.ext hab
  have hrootMem : root ∈ colorNeighborhood c q (f x) := by
    rw [mem_colorNeighborhood]
    constructor
    · exact Ne.symm (e x).property
    · rw [c.color_symm]
      exact hrootColor
  have hcard :
      (colorNeighborhood (pullbackColoring c f) q x).card =
        ((colorNeighborhood c q (f x)).erase root).card := by
    apply Finset.card_bij (fun y _hy => f y)
    · intro y hy
      rw [Finset.mem_erase, mem_colorNeighborhood]
      have hy' := (mem_colorNeighborhood
        (pullbackColoring c f) q x y).mp hy
      exact ⟨(e y).property, hf.ne hy'.1, hy'.2⟩
    · intro a ha b hb hab
      exact hf hab
    · intro v hv
      have hv' := Finset.mem_erase.mp hv
      let ve : {z : V // z ≠ root} := ⟨v, hv'.1⟩
      let y : W := e.symm ve
      refine ⟨y, ?_, ?_⟩
      · rw [mem_colorNeighborhood]
        have hvn := (mem_colorNeighborhood c q (f x) v).mp hv'.2
        constructor
        · intro hyx
          apply hvn.1
          calc
            v = f y := by simp [f, y, ve]
            _ = f x := congrArg f hyx
        · change c (f x) (f y) = q
          simpa [f, y, ve] using hvn.2
      · simp [f, y, ve]
  change (colorNeighborhood (pullbackColoring c f) q x).card + 1 =
    (colorNeighborhood c q (f x)).card
  have hpositive : 1 ≤ (colorNeighborhood c q (f x)).card :=
    Finset.one_le_card.mpr ⟨root, hrootMem⟩
  calc
    (colorNeighborhood (pullbackColoring c f) q x).card + 1 =
        ((colorNeighborhood c q (f x)).erase root).card + 1 := by
      rw [hcard]
    _ = (colorNeighborhood c q (f x)).card := by
      rw [Finset.card_erase_of_mem hrootMem]
      omega

/-! ## The canonical relabeling preserves the root block -/

theorem normalizedHost_root_hostRelabelVertex
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (x : Fin 60) :
    normalizedHost data data.root (hostRelabelVertex data x) =
      indexedRootColor (vertexBlock (cnfProfile data.profile) x) := by
  let coordinates := blockPositionEquiv (cnfProfile data.profile)
  rcases hxcoord : coordinates x with ⟨block, pos⟩
  have hx :
      blockVertex (cnfProfile data.profile) block pos.val = x := by
    apply coordinates.injective
    rw [blockPositionEquiv_blockVertex
      (cnfProfile data.profile) block pos.val pos.isLt]
    exact hxcoord.symm
  have hblock :
      vertexBlock (cnfProfile data.profile) x = block := by
    simp [vertexBlock, coordinates, hxcoord]
  rw [hblock, ← hx]
  rw [hostRelabelVertex, hostRelabelEquiv_blockVertex_val]
  exact ((mem_colorNeighborhood (normalizedHost data)
    (indexedRootColor block) data.root
    (blockLocalEquiv data block pos).val).mp
      (blockLocalEquiv data block pos).property).2

/-- Exact own-colour degree transport from the canonical non-root star back
to the normalized host. -/
theorem canonical_own_degree_add_one_eq_normalized
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (x : Fin 60) :
    colorDegree (canonicalStarColoring data)
        (vertexBlock (cnfProfile data.profile) x) x + 1 =
      colorDegree (normalizedHost data)
        (normalizedHost data data.root (hostRelabelVertex data x))
        (hostRelabelVertex data x) := by
  let block := vertexBlock (cnfProfile data.profile) x
  have hroot := normalizedHost_root_hostRelabelVertex data x
  have hroot' :
      normalizedHost data data.root (hostRelabelEquiv data x).val =
        indexedRootColor block := by
    simpa [hostRelabelVertex, block] using hroot
  have hdelete := colorDegree_pullback_nonRoot_add_one
    (normalizedHost data) data.root (hostRelabelEquiv data)
    (indexedRootColor block) x hroot'
  rw [hroot]
  rw [canonicalStarColoring, colorDegree_mapEdgeColors]
  change colorDegree
      (pullbackColoring (normalizedHost data)
        (fun y => (hostRelabelEquiv data y).val))
      (singleRootFourColorEquivFin4.symm
        (vertexBlock (cnfProfile data.profile) x)) x + 1 =
    colorDegree (normalizedHost data)
      (singleRootFourColorEquivFin4.symm
        (vertexBlock (cnfProfile data.profile) x))
      (hostRelabelEquiv data x).val
  simpa [indexedRootColor, block] using hdelete

/-! ## Exact support transport -/

/-- Canonical non-root vertices whose own root-block colour has degree at
least fourteen inside the non-root `K60`. -/
noncomputable def canonicalHighOwnDegreeSupport
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) : Finset (Fin 60) :=
  Finset.univ.filter fun x =>
    14 ≤ colorDegree (canonicalStarColoring data)
      (vertexBlock (cnfProfile data.profile) x) x

@[simp] theorem mem_canonicalHighOwnDegreeSupport
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (x : Fin 60) :
    x ∈ canonicalHighOwnDegreeSupport data ↔
      14 ≤ colorDegree (canonicalStarColoring data)
        (vertexBlock (cnfProfile data.profile) x) x := by
  simp [canonicalHighOwnDegreeSupport]

theorem mem_canonicalHigh_iff_hostHigh
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (x : Fin 60) :
    x ∈ canonicalHighOwnDegreeSupport data ↔
      hostRelabelVertex data x ∈
        highOwnNeighborSupport (normalizedHost data) data.root := by
  rw [mem_canonicalHighOwnDegreeSupport,
    mem_highOwnNeighborSupport]
  have hdegree := canonical_own_degree_add_one_eq_normalized data x
  have hne : hostRelabelVertex data x ≠ data.root := by
    simpa [hostRelabelVertex] using (hostRelabelEquiv data x).property
  constructor
  · intro hhigh
    refine ⟨hne, ?_⟩
    omega
  · rintro ⟨_hne, hhigh⟩
    omega

theorem canonicalHighOwnDegreeSupport_card_eq_host
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    (canonicalHighOwnDegreeSupport data).card =
      (highOwnNeighborSupport (normalizedHost data) data.root).card := by
  apply Finset.card_bij
      (fun x (_hx : x ∈ canonicalHighOwnDegreeSupport data) =>
        hostRelabelVertex data x)
  · intro x hx
    exact (mem_canonicalHigh_iff_hostHigh data x).mp hx
  · intro x hx y hy hxy
    exact hostRelabelVertex_injective data hxy
  · intro endpoint hendpoint
    have hne :=
      (mem_highOwnNeighborSupport
        (normalizedHost data) data.root endpoint).mp hendpoint |>.1
    let endpointNonRoot : NonRoot data := ⟨endpoint, hne⟩
    let x : Fin 60 := (hostRelabelEquiv data).symm endpointNonRoot
    have hximage : hostRelabelVertex data x = endpoint := by
      simp [hostRelabelVertex, x, endpointNonRoot]
    refine ⟨x, ?_, hximage⟩
    apply (mem_canonicalHigh_iff_hostHigh data x).mpr
    simpa [hximage] using hendpoint

/-- The normalized-host lower bound therefore survives canonization without
any loss. -/
theorem canonicalHighOwnDegreeSupport_card_ge_thirtyTwo
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (hhigh : 32 ≤ highOwnNeighborCount
      (normalizedHost data) data.root) :
    32 ≤ (canonicalHighOwnDegreeSupport data).card := by
  rw [canonicalHighOwnDegreeSupport_card_eq_host]
  exact hhigh

/-! ## The last 46 canonical positions -/

/-- High canonical vertices among labels `14,...,59`.  For profile D this is
exactly its `K15 + K15 + K16` tail. -/
noncomputable def canonicalHighTailDegreeSupport
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) : Finset (Fin 60) :=
  (canonicalHighOwnDegreeSupport data).filter fun x => 14 ≤ x.val

@[simp] theorem mem_canonicalHighTailDegreeSupport
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (x : Fin 60) :
    x ∈ canonicalHighTailDegreeSupport data ↔
      x ∈ canonicalHighOwnDegreeSupport data ∧ 14 ≤ x.val := by
  simp [canonicalHighTailDegreeSupport]

theorem canonicalHighTailDegreeSupport_card_ge_eighteen
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (hhigh : 32 ≤ highOwnNeighborCount
      (normalizedHost data) data.root) :
    18 ≤ (canonicalHighTailDegreeSupport data).card := by
  let high := canonicalHighOwnDegreeSupport data
  let first := high.filter fun x => x.val < 14
  let tail := high.filter fun x => 14 ≤ x.val
  have hfirst : first.card ≤ 14 := by
    have hsubset : first ⊆
        (Finset.univ : Finset (Fin 60)).filter fun x => x.val < 14 := by
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx'⟩
    calc
      first.card ≤
          ((Finset.univ : Finset (Fin 60)).filter
            fun x => x.val < 14).card := Finset.card_le_card hsubset
      _ = 14 := by decide
  have hsplit : high.card = first.card + tail.card := by
    have hdisjoint : Disjoint first tail := by
      rw [Finset.disjoint_left]
      intro x hxfirst hxtail
      have hlt := (Finset.mem_filter.mp hxfirst).2
      have hge := (Finset.mem_filter.mp hxtail).2
      omega
    have hunion : first ∪ tail = high := by
      ext x
      simp only [first, tail, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (hx | hx) <;> exact hx.1
      · intro hx
        by_cases hlt : x.val < 14
        · exact Or.inl ⟨hx, hlt⟩
        · exact Or.inr ⟨hx, by omega⟩
    rw [← hunion]
    exact Finset.card_union_of_disjoint hdisjoint
  have hcanonical : 32 ≤ high.card := by
    simpa [high] using
      canonicalHighOwnDegreeSupport_card_ge_thirtyTwo data hhigh
  have htail : tail = canonicalHighTailDegreeSupport data := by
    rfl
  rw [htail] at hsplit
  omega

/-! ## A high endpoint in explicit canonical block coordinates -/

/-- Every canonical label at least fourteen lies outside block zero, in all
four root profiles.  The first block has order `12`, `13`, or `14`. -/
theorem vertexBlock_ne_zero_of_fourteen_le
    (profile : Profile) (x : Fin 60) (hx : 14 ≤ x.val) :
    vertexBlock profile x ≠ 0 := by
  intro hzero
  let coordinates := blockPositionEquiv profile
  rcases hcoord : coordinates x with ⟨block, pos⟩
  have hblock : block = 0 := by
    simpa [vertexBlock, coordinates, hcoord] using hzero
  have hxvertex : blockVertex profile block pos.val = x := by
    apply coordinates.injective
    calc
      coordinates (blockVertex profile block pos.val) =
          ⟨block, pos⟩ := by
        simpa [coordinates] using
          blockPositionEquiv_blockVertex
            profile block pos.val pos.isLt
      _ = coordinates x := hcoord.symm
  have hval := congrArg Fin.val hxvertex
  rw [blockVertex_val profile block pos.isLt] at hval
  have hpos := pos.isLt
  subst block
  cases profile <;>
    simp [blockStart, blockSize, profileSizes] at hval hpos <;> omega

/-- The high-root lower bound supplies an explicit high endpoint in a
nonzero canonical root block.  This is the coordinate form consumed by the
uniform foreign-block support bounds. -/
theorem exists_high_blockPosition_outside_zero
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (hhigh : 32 ≤ highOwnNeighborCount
      (normalizedHost data) data.root) :
    ∃ source : Fin 4,
      ∃ i : Fin (blockSize (cnfProfile data.profile) source),
        source ≠ 0 ∧
          14 ≤ colorDegree (canonicalStarColoring data) source
            (blockVertex (cnfProfile data.profile) source i.val) := by
  have htail := canonicalHighTailDegreeSupport_card_ge_eighteen data hhigh
  have hnonempty : (canonicalHighTailDegreeSupport data).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hnonempty
  have hxparts := (mem_canonicalHighTailDegreeSupport data x).mp hx
  have hxhigh := (mem_canonicalHighOwnDegreeSupport data x).mp hxparts.1
  let coordinates := blockPositionEquiv (cnfProfile data.profile)
  rcases hcoord : coordinates x with ⟨source, pos⟩
  have hxvertex :
      blockVertex (cnfProfile data.profile) source pos.val = x := by
    apply coordinates.injective
    rw [blockPositionEquiv_blockVertex
      (cnfProfile data.profile) source pos.val pos.isLt]
    exact hcoord.symm
  have hblock :
      vertexBlock (cnfProfile data.profile) x = source := by
    simp [vertexBlock, coordinates, hcoord]
  have hsource : source ≠ 0 := by
    intro hzero
    apply vertexBlock_ne_zero_of_fourteen_le
      (cnfProfile data.profile) x hxparts.2
    simpa [hblock] using hzero
  refine ⟨source, pos, hsource, ?_⟩
  simpa [hblock, hxvertex] using hxhigh

#print axioms R4333.CanonicalHighOwnTransport61.colorDegree_pullback_nonRoot_add_one
#print axioms R4333.CanonicalHighOwnTransport61.normalizedHost_root_hostRelabelVertex
#print axioms R4333.CanonicalHighOwnTransport61.canonical_own_degree_add_one_eq_normalized
#print axioms R4333.CanonicalHighOwnTransport61.canonicalHighOwnDegreeSupport_card_eq_host
#print axioms R4333.CanonicalHighOwnTransport61.canonicalHighOwnDegreeSupport_card_ge_thirtyTwo
#print axioms R4333.CanonicalHighOwnTransport61.canonicalHighTailDegreeSupport_card_ge_eighteen
#print axioms R4333.CanonicalHighOwnTransport61.vertexBlock_ne_zero_of_fourteen_le
#print axioms R4333.CanonicalHighOwnTransport61.exists_high_blockPosition_outside_zero

end CanonicalHighOwnTransport61
end R4333
