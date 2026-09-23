import R4333Lean.Attaching61
import Mathlib.Data.Fintype.EquivFin

/-!
# The six-region partition of an attaching pair

For two distinct roots joined by a colour other than `delta`, their two
`delta`-neighbourhoods divide the host into the roots, the common part, the
two one-sided parts, and the outside complement.  This is ordinary finite-set
combinatorics; no critical-template or certificate data occurs here.
-/

namespace R4333

open Finset

/-- The six pieces determined by an ordered pair of attaching roots. -/
inductive AttachingRegion where
  | leftRoot
  | rightRoot
  | common
  | leftOnly
  | rightOnly
  | outside
  deriving DecidableEq, Fintype, Repr

/-- The concrete finite set represented by each of the six region labels. -/
def attachingRegionFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V) :
    AttachingRegion → Finset V
  | .leftRoot => {u}
  | .rightRoot => {v}
  | .common => colorNeighborhood c delta u ∩ colorNeighborhood c delta v
  | .leftOnly => colorNeighborhood c delta u \ colorNeighborhood c delta v
  | .rightOnly => colorNeighborhood c delta v \ colorNeighborhood c delta u
  | .outside => Finset.univ \ ({u, v} ∪
      (colorNeighborhood c delta u ∪ colorNeighborhood c delta v))

@[simp] theorem mem_attachingRegion_leftRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v x : V) :
    x ∈ attachingRegionFinset c delta u v .leftRoot ↔ x = u := by
  simp [attachingRegionFinset]

@[simp] theorem mem_attachingRegion_rightRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v x : V) :
    x ∈ attachingRegionFinset c delta u v .rightRoot ↔ x = v := by
  simp [attachingRegionFinset]

@[simp] theorem mem_attachingRegion_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v x : V) :
    x ∈ attachingRegionFinset c delta u v .common ↔
      x ∈ colorNeighborhood c delta u ∧
      x ∈ colorNeighborhood c delta v := by
  simp [attachingRegionFinset]

@[simp] theorem mem_attachingRegion_leftOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v x : V) :
    x ∈ attachingRegionFinset c delta u v .leftOnly ↔
      x ∈ colorNeighborhood c delta u ∧
      x ∉ colorNeighborhood c delta v := by
  simp [attachingRegionFinset]

@[simp] theorem mem_attachingRegion_rightOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v x : V) :
    x ∈ attachingRegionFinset c delta u v .rightOnly ↔
      x ∈ colorNeighborhood c delta v ∧
      x ∉ colorNeighborhood c delta u := by
  simp [attachingRegionFinset]

@[simp] theorem mem_attachingRegion_outside
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v x : V) :
    x ∈ attachingRegionFinset c delta u v .outside ↔
      x ≠ u ∧ x ≠ v ∧
      x ∉ colorNeighborhood c delta u ∧
      x ∉ colorNeighborhood c delta v := by
  simp [attachingRegionFinset]

/-- For an attaching edge, neither root belongs to either selected
`delta`-neighbourhood. -/
theorem attaching_roots_not_mem_delta_neighborhoods
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (_huv : u ≠ v) (hedge : c u v ≠ delta) :
    u ∉ colorNeighborhood c delta u ∧
    u ∉ colorNeighborhood c delta v ∧
    v ∉ colorNeighborhood c delta u ∧
    v ∉ colorNeighborhood c delta v := by
  have huLeft : u ∉ colorNeighborhood c delta u := by simp
  have hvRight : v ∉ colorNeighborhood c delta v := by simp
  have hvLeft : v ∉ colorNeighborhood c delta u := by
    simp [mem_colorNeighborhood, hedge]
  have huRight : u ∉ colorNeighborhood c delta v := by
    intro hu
    have hcolor := (mem_colorNeighborhood c delta v u).mp hu |>.2
    apply hedge
    exact (c.color_symm u v).trans hcolor
  exact ⟨huLeft, huRight, hvLeft, hvRight⟩

/-- Distinct region labels denote disjoint finite sets. -/
theorem attachingRegionFinset_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (huv : u ≠ v) (hedge : c u v ≠ delta) :
    ∀ r s : AttachingRegion, r ≠ s →
      Disjoint (attachingRegionFinset c delta u v r)
        (attachingRegionFinset c delta u v s) := by
  intro r s hrs
  obtain ⟨huLeft, huRight, hvLeft, hvRight⟩ :=
    attaching_roots_not_mem_delta_neighborhoods c delta u v huv hedge
  have hvu : v ≠ u := Ne.symm huv
  fin_cases r <;> fin_cases s <;>
    simp_all [attachingRegionFinset, Finset.disjoint_left,
      mem_colorNeighborhood] <;> aesop

/-- Every host vertex belongs to one and only one of the six regions. -/
theorem existsUnique_mem_attachingRegionFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v x : V)
    (huv : u ≠ v) (hedge : c u v ≠ delta) :
    ∃! r : AttachingRegion, x ∈ attachingRegionFinset c delta u v r := by
  have hexists : ∃ r : AttachingRegion,
      x ∈ attachingRegionFinset c delta u v r := by
    by_cases hxu : x = u
    · exact ⟨.leftRoot, by simp [hxu]⟩
    by_cases hxv : x = v
    · exact ⟨.rightRoot, by simp [hxv]⟩
    by_cases hxLeft : x ∈ colorNeighborhood c delta u
    · by_cases hxRight : x ∈ colorNeighborhood c delta v
      · exact ⟨.common, by simp [hxLeft, hxRight]⟩
      · exact ⟨.leftOnly, by simp [hxLeft, hxRight]⟩
    · by_cases hxRight : x ∈ colorNeighborhood c delta v
      · exact ⟨.rightOnly, by simp [hxLeft, hxRight]⟩
      · exact ⟨.outside, by simp [hxu, hxv, hxLeft, hxRight]⟩
  obtain ⟨r, hr⟩ := hexists
  refine ⟨r, hr, ?_⟩
  intro s hs
  by_contra hsr
  have hrs : r ≠ s := fun h ↦ hsr h.symm
  have hd := attachingRegionFinset_pairwise_disjoint
    c delta u v huv hedge r s hrs
  exact (Finset.disjoint_left.mp hd) hr hs

/-- The common region has the stipulated intersection cardinality. -/
theorem attachingRegion_common_card
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k) :
    #(attachingRegionFinset c delta u v .common) = k := by
  simpa [attachingRegionFinset] using hinter

/-- The left-only region has cardinality `du - k`. -/
theorem attachingRegion_leftOnly_card
    {V : Type*} [Fintype V] [DecidableEq V] {du k : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (hdu : colorDegree c delta u = du)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k) :
    #(attachingRegionFinset c delta u v .leftOnly) = du - k := by
  have hleft : #(colorNeighborhood c delta u) = du := by
    simpa [colorDegree] using hdu
  have hinter' : #(colorNeighborhood c delta v ∩
      colorNeighborhood c delta u) = k := by
    simpa [Finset.inter_comm] using hinter
  simp [attachingRegionFinset, Finset.card_sdiff, hleft, hinter']

/-- The right-only region has cardinality `dv - k`. -/
theorem attachingRegion_rightOnly_card
    {V : Type*} [Fintype V] [DecidableEq V] {dv k : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (hdv : colorDegree c delta v = dv)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k) :
    #(attachingRegionFinset c delta u v .rightOnly) = dv - k := by
  have hright : #(colorNeighborhood c delta v) = dv := by
    simpa [colorDegree] using hdv
  simp [attachingRegionFinset, Finset.card_sdiff, hright, hinter]

/-- The actual intersection bounds imply the subtraction side conditions
`k ≤ du` and `k ≤ dv`. -/
theorem attaching_intersection_le_degrees
    {V : Type*} [Fintype V] [DecidableEq V] {du dv k : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (hdu : colorDegree c delta u = du)
    (hdv : colorDegree c delta v = dv)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k) :
    k ≤ du ∧ k ≤ dv := by
  have hleft := Finset.card_mono
    (Finset.inter_subset_left :
      colorNeighborhood c delta u ∩ colorNeighborhood c delta v ⊆
        colorNeighborhood c delta u)
  have hright := Finset.card_mono
    (Finset.inter_subset_right :
      colorNeighborhood c delta u ∩ colorNeighborhood c delta v ⊆
        colorNeighborhood c delta v)
  have hleftCard : #(colorNeighborhood c delta u) = du := by
    simpa [colorDegree] using hdu
  have hrightCard : #(colorNeighborhood c delta v) = dv := by
    simpa [colorDegree] using hdv
  omega

/-- Before simplifying natural-number subtraction, the outside region has
the truncation-safe cardinality `61 - (2 + (du + dv - k))`. -/
theorem attachingRegion_outside_card_raw
    {V : Type*} [Fintype V] [DecidableEq V] {du dv k : ℕ}
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (huv : u ≠ v) (hedge : c u v ≠ delta)
    (hdu : colorDegree c delta u = du)
    (hdv : colorDegree c delta v = dv)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k) :
    #(attachingRegionFinset c delta u v .outside) =
      61 - (2 + (du + dv - k)) := by
  let A := colorNeighborhood c delta u
  let B := colorNeighborhood c delta v
  have hA : #A = du := by simpa [A, colorDegree] using hdu
  have hB : #B = dv := by simpa [B, colorDegree] using hdv
  have hAB : #(A ∩ B) = k := by simpa [A, B] using hinter
  obtain ⟨huA, huB, hvA, hvB⟩ :=
    attaching_roots_not_mem_delta_neighborhoods c delta u v huv hedge
  have hrootDisjoint : Disjoint ({u, v} : Finset V) (A ∪ B) := by
    rw [Finset.disjoint_left]
    intro x hxRoot hxUnion
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxRoot
    simp only [Finset.mem_union] at hxUnion
    rcases hxRoot with rfl | rfl <;> rcases hxUnion with hx | hx <;>
      simp_all [A, B]
  have hrootCard : #({u, v} : Finset V) = 2 := by
    simp [huv]
  have hunionCard : #(A ∪ B) = du + dv - k := by
    rw [Finset.card_union, hA, hB, hAB]
  have hremovedCard : #(({u, v} : Finset V) ∪ (A ∪ B)) =
      2 + (du + dv - k) := by
    rw [Finset.card_union_of_disjoint hrootDisjoint, hrootCard, hunionCard]
  rw [attachingRegionFinset, Finset.card_sdiff_of_subset (by simp),
    Finset.card_univ, hcard]
  simpa [A, B] using congrArg (fun n ↦ 61 - n) hremovedCard

/-- In the attaching range, `du + dv ≤ 59` removes all truncation ambiguity
and gives the convenient outside size `59 - du - dv + k`. -/
theorem attachingRegion_outside_card
    {V : Type*} [Fintype V] [DecidableEq V] {du dv k : ℕ}
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (huv : u ≠ v) (hedge : c u v ≠ delta)
    (hdu : colorDegree c delta u = du)
    (hdv : colorDegree c delta v = dv)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k)
    (hdegreeSum : du + dv ≤ 59) :
    #(attachingRegionFinset c delta u v .outside) =
      59 - du - dv + k := by
  have hraw := attachingRegion_outside_card_raw hcard c delta u v
    huv hedge hdu hdv hinter
  have hk := attaching_intersection_le_degrees c delta u v hdu hdv hinter
  omega

/-- All six cardinalities in one statement, ready to instantiate a finite
encoding. -/
theorem attachingRegion_cards
    {V : Type*} [Fintype V] [DecidableEq V] {du dv k : ℕ}
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (huv : u ≠ v) (hedge : c u v ≠ delta)
    (hdu : colorDegree c delta u = du)
    (hdv : colorDegree c delta v = dv)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k)
    (hdegreeSum : du + dv ≤ 59) :
    #(attachingRegionFinset c delta u v .leftRoot) = 1 ∧
    #(attachingRegionFinset c delta u v .rightRoot) = 1 ∧
    #(attachingRegionFinset c delta u v .common) = k ∧
    #(attachingRegionFinset c delta u v .leftOnly) = du - k ∧
    #(attachingRegionFinset c delta u v .rightOnly) = dv - k ∧
    #(attachingRegionFinset c delta u v .outside) =
      59 - du - dv + k := by
  exact ⟨by simp [attachingRegionFinset],
    by simp [attachingRegionFinset],
    attachingRegion_common_card c delta u v hinter,
    attachingRegion_leftOnly_card c delta u v hdu hinter,
    attachingRegion_rightOnly_card c delta u v hdv hinter,
    attachingRegion_outside_card hcard c delta u v huv hedge
      hdu hdv hinter hdegreeSum⟩

/-- The subtype of vertices in one selected region. -/
abbrev AttachingRegionVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (r : AttachingRegion) :=
  {x : V // x ∈ attachingRegionFinset c delta u v r}

theorem attachingRegionVertex_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (r : AttachingRegion) :
    Fintype.card (AttachingRegionVertex c delta u v r) =
      #(attachingRegionFinset c delta u v r) := by
  exact Fintype.card_coe _

/-- Choose labels `Fin n` for any region whose exact cardinality is known. -/
noncomputable def attachingRegionEquivFin
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (r : AttachingRegion)
    (hregion : #(attachingRegionFinset c delta u v r) = n) :
    Fin n ≃ AttachingRegionVertex c delta u v r :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, attachingRegionVertex_card, hregion])

/-- The six chosen finite labelings needed by a later finite CNF. -/
structure AttachingPartitionLabels
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (du dv k : ℕ) where
  leftRoot : Fin 1 ≃ AttachingRegionVertex c delta u v .leftRoot
  rightRoot : Fin 1 ≃ AttachingRegionVertex c delta u v .rightRoot
  common : Fin k ≃ AttachingRegionVertex c delta u v .common
  leftOnly : Fin (du - k) ≃ AttachingRegionVertex c delta u v .leftOnly
  rightOnly : Fin (dv - k) ≃ AttachingRegionVertex c delta u v .rightOnly
  outside : Fin (59 - du - dv + k) ≃
    AttachingRegionVertex c delta u v .outside

/-- Construct all six region labelings from the degree and intersection
equalities. -/
noncomputable def attachingPartitionLabels
    {V : Type*} [Fintype V] [DecidableEq V] {du dv k : ℕ}
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V)
    (huv : u ≠ v) (hedge : c u v ≠ delta)
    (hdu : colorDegree c delta u = du)
    (hdv : colorDegree c delta v = dv)
    (hinter : #(colorNeighborhood c delta u ∩
      colorNeighborhood c delta v) = k)
    (hdegreeSum : du + dv ≤ 59) :
    AttachingPartitionLabels c delta u v du dv k where
  leftRoot := attachingRegionEquivFin c delta u v .leftRoot (by
    simp [attachingRegionFinset])
  rightRoot := attachingRegionEquivFin c delta u v .rightRoot (by
    simp [attachingRegionFinset])
  common := attachingRegionEquivFin c delta u v .common
    (attachingRegion_common_card c delta u v hinter)
  leftOnly := attachingRegionEquivFin c delta u v .leftOnly
    (attachingRegion_leftOnly_card c delta u v hdu hinter)
  rightOnly := attachingRegionEquivFin c delta u v .rightOnly
    (attachingRegion_rightOnly_card c delta u v hdv hinter)
  outside := attachingRegionEquivFin c delta u v .outside
    (attachingRegion_outside_card hcard c delta u v huv hedge
      hdu hdv hinter hdegreeSum)

#print axioms R4333.attachingRegionFinset_pairwise_disjoint
#print axioms R4333.existsUnique_mem_attachingRegionFinset
#print axioms R4333.attachingRegion_cards
#print axioms R4333.attachingRegion_outside_card
#print axioms R4333.attachingPartitionLabels

end R4333
