import R4333Lean.FiniteObstructionInterface
import R4333Lean.ColorRelabel

/-!
# A canonical finite host for an attaching partition

The six individually labelled regions combine into one dependent finite sum.
This file proves that the sum is equivalent to the original host and pulls
the colouring back along that equivalence.  A later CNF can therefore use one
canonical vertex type without trusting an external relabelling program.
-/

namespace R4333

/-- The cardinality assigned to each of the six attaching regions. -/
def attachingRegionSize (du dv k : ℕ) : AttachingRegion → ℕ
  | .leftRoot => 1
  | .rightRoot => 1
  | .common => k
  | .leftOnly => du - k
  | .rightOnly => dv - k
  | .outside => 59 - du - dv + k

/-- The canonical dependent sum of the six labelled regions. -/
abbrev CanonicalAttachingVertex (du dv k : ℕ) :=
  Σ r : AttachingRegion, Fin (attachingRegionSize du dv k r)

/-- Read the appropriate component equivalence from all six partition
labels. -/
def AttachingPartitionLabels.regionEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k)
    (r : AttachingRegion) :
    Fin (attachingRegionSize du dv k r) ≃
      AttachingRegionVertex c delta u v r :=
  match r with
  | .leftRoot => labels.leftRoot
  | .rightRoot => labels.rightRoot
  | .common => labels.common
  | .leftOnly => labels.leftOnly
  | .rightOnly => labels.rightOnly
  | .outside => labels.outside

/-- Forget a canonical region label and return its actual host vertex. -/
def canonicalAttachingToHost
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k) :
    CanonicalAttachingVertex du dv k → V
  | ⟨r, i⟩ => (labels.regionEquiv r i).1

theorem canonicalAttachingToHost_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k)
    (huv : u ≠ v) (hedge : c u v ≠ delta) :
    Function.Injective (canonicalAttachingToHost labels) := by
  rintro ⟨r, i⟩ ⟨s, j⟩ hvalue
  change (labels.regionEquiv r i).1 = (labels.regionEquiv s j).1 at hvalue
  by_cases hrs : r = s
  · subst s
    have hij : i = j := by
      apply (labels.regionEquiv r).injective
      apply Subtype.ext
      exact hvalue
    subst j
    rfl
  · have hd := attachingRegionFinset_pairwise_disjoint
      c delta u v huv hedge r s hrs
    have hi := (labels.regionEquiv r i).property
    have hj := (labels.regionEquiv s j).property
    have hjsame : (labels.regionEquiv r i).1 ∈
        attachingRegionFinset c delta u v s := by
      rw [hvalue]
      exact hj
    exfalso
    exact (Finset.disjoint_left.mp hd) hi hjsame

theorem canonicalAttachingToHost_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k)
    (huv : u ≠ v) (hedge : c u v ≠ delta) :
    Function.Surjective (canonicalAttachingToHost labels) := by
  intro x
  obtain ⟨r, hx, _⟩ :=
    existsUnique_mem_attachingRegionFinset c delta u v x huv hedge
  let xr : AttachingRegionVertex c delta u v r := ⟨x, hx⟩
  let i := (labels.regionEquiv r).symm xr
  refine ⟨⟨r, i⟩, ?_⟩
  simp [canonicalAttachingToHost, i, xr]

/-- The six labels form one equivalence from the canonical dependent sum to
the actual host. -/
noncomputable def canonicalAttachingEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k)
    (huv : u ≠ v) (hedge : c u v ≠ delta) :
    CanonicalAttachingVertex du dv k ≃ V :=
  Equiv.ofBijective (canonicalAttachingToHost labels)
    ⟨canonicalAttachingToHost_injective labels huv hedge,
      canonicalAttachingToHost_surjective labels huv hedge⟩

/-- Pull the original colouring back to the canonical six-region host. -/
noncomputable def canonicalAttachingColoring
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k)
    (huv : u ≠ v) (hedge : c u v ≠ delta) :
    EdgeColoring (CanonicalAttachingVertex du dv k) FourColor :=
  relabelVertices c (canonicalAttachingEquiv labels huv hedge)

theorem canonicalAttachingColoring_noMono
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k)
    (huv : u ≠ v) (hedge : c u v ≠ delta)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle
      (canonicalAttachingColoring labels huv hedge) :=
  noMono_relabelVertices c (canonicalAttachingEquiv labels huv hedge) hc

theorem canonicalAttachingVertex_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {delta : FourColor} {u v : V}
    {du dv k : ℕ}
    (labels : AttachingPartitionLabels c delta u v du dv k)
    (huv : u ≠ v) (hedge : c u v ≠ delta)
    (hcard : Fintype.card V = 61) :
    Fintype.card (CanonicalAttachingVertex du dv k) = 61 := by
  rw [Fintype.card_congr (canonicalAttachingEquiv labels huv hedge), hcard]

namespace FiniteObstructionInterface

/-- The canonical-host equivalence carried by a complete finite obstruction
interface. -/
noncomputable def canonicalEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    CanonicalAttachingVertex
        (colorDegree c delta u)
        (colorDegree c delta v)
        (Finset.card (colorNeighborhood c delta u ∩
          colorNeighborhood c delta v)) ≃ V :=
  canonicalAttachingEquiv interface.partitionLabels
    interface.attaching.1 interface.attaching.2.1

/-- The actual hypothetical colouring, on the canonical six-region vertex
type used by a future finite formula. -/
noncomputable def canonicalColoring
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    EdgeColoring
      (CanonicalAttachingVertex
        (colorDegree c delta u)
        (colorDegree c delta v)
        (Finset.card (colorNeighborhood c delta u ∩
          colorNeighborhood c delta v)))
      FourColor :=
  relabelVertices c interface.canonicalEquiv

theorem canonicalColoring_noMono
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    NoMonochromaticTriangle interface.canonicalColoring :=
  noMono_relabelVertices c interface.canonicalEquiv hc

theorem canonicalVertex_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    Fintype.card
      (CanonicalAttachingVertex
        (colorDegree c delta u)
        (colorDegree c delta v)
        (Finset.card (colorNeighborhood c delta u ∩
          colorNeighborhood c delta v))) = 61 :=
  canonicalAttachingVertex_card interface.partitionLabels
    interface.attaching.1 interface.attaching.2.1 interface.hostCard

/-- Exact 35-row degree selectors for every vertex after the canonical host
relabeling. -/
theorem exists_canonicalDegreeTargetSelection
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v) :
    Nonempty (DegreeTargetSelection61 interface.canonicalColoring) :=
  exists_degreeTargetSelection61 interface.canonicalVertex_card
    interface.canonicalColoring interface.canonicalColoring_noMono

end FiniteObstructionInterface

#print axioms R4333.canonicalAttachingToHost_injective
#print axioms R4333.canonicalAttachingEquiv
#print axioms R4333.canonicalAttachingColoring_noMono
#print axioms R4333.FiniteObstructionInterface.canonicalColoring_noMono
#print axioms R4333.FiniteObstructionInterface.exists_canonicalDegreeTargetSelection

end R4333
