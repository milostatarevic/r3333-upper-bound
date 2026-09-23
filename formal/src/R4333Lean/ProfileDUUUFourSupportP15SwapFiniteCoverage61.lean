import R4333Lean.ProfileDUUUFourSupportP15SwapData61
import R4333Lean.ProfileDUUUFourSupportBlockTwoSwap61
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitTransportUUU2P15

/-!
# Kernel-checked finite coverage for the P15 equal-K15 swap quotient

The semantic module proves that the UUU block-two transport acts on the
four-support restored matrix by exchanging the two five-coordinate groups
and host colours one and two.  This file checks the remaining finite lookup:
each of the 372 already-quotiented ordered leaves is either one of the stored
189 seeds or the exact swap image of its seed.

The lookup is not accepted as an arbitrary permutation table.  For every
leaf, ordinary kernel reduction also checks that the swapped 14-vertex
matrix is the advertised partner after one explicit free-four permutation
and two explicit strong-support stabilizer actions.
-/

namespace R4333
namespace ProfileDUUUFourSupportP15SwapFiniteCoverage61

open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
open ProfileDUUUDegreeTenCatalogOrbitTransportUUU2P15
open ProfileDUUUFourSupportP15SwapData61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev OrderedLeaf := ProfileDUUUFourSupportP15SwapData61.OrderedLeaf
abbrev SwapSeed := ProfileDUUUFourSupportP15SwapData61.SwapSeed

/-! ## Exact packed matrices -/

def matrixEdgeIndex (u v : Fin 14) : Nat :=
  let left := min u.val v.val
  let right := max u.val v.val
  left * (27 - left) / 2 + (right - left - 1)

def orderedMatrixColor (leaf : OrderedLeaf) (u v : Fin 14) : Fin 4 :=
  let edge := matrixEdgeIndex u v
  let row :=
    (ProfileDUUUFourSupportP15SwapData61.orderedMatrixByteTable[leaf.val]?).getD #[]
  let byte := (row[edge / 4]?).getD 0
  Fin.ofNat 4 ((byte >>> (2 * (edge % 4))) % 4)

theorem orderedMatrixByteTable_size :
    ProfileDUUUFourSupportP15SwapData61.orderedMatrixByteTable.size = 372 := by
  decide

theorem orderedMatrixColor_symm (leaf : OrderedLeaf) (u v : Fin 14) :
    orderedMatrixColor leaf u v = orderedMatrixColor leaf v u := by
  simp [orderedMatrixColor, matrixEdgeIndex, min_comm, max_comm]

/-! ## The computable form of the semantic swap -/

/-- The same `4|5|5` coordinate involution used by the semantic transport,
written as a small table so the finite matrix check stays inexpensive. -/
def checkedCoordinateSwap : Fin 14 → Fin 14 :=
  ![0, 1, 2, 3, 9, 10, 11, 12, 13, 4, 5, 6, 7, 8]

/-- Swap host colours one and two, fixing zero and three. -/
def checkedColorSwap : Fin 4 → Fin 4 := ![0, 2, 1, 3]

theorem checkedCoordinateSwap_eq_semantic (i : Fin 14) :
    checkedCoordinateSwap i =
      ProfileDUUUFourSupportBlockTwoSwap61.restoredK15CoordinateSwap i := by
  fin_cases i <;> decide

theorem checkedColorSwap_eq_semantic (q : Fin 4) :
    checkedColorSwap q = ProfileDFourRowKindSymmetry.hostColorPerm q := by
  fin_cases q <;> rfl

def rawSwapMatrixColor (leaf : OrderedLeaf) (u v : Fin 14) : Fin 4 :=
  checkedColorSwap
    (orderedMatrixColor leaf (checkedCoordinateSwap u)
      (checkedCoordinateSwap v))

theorem rawSwapMatrixColor_eq_semantic (leaf : OrderedLeaf)
    (u v : Fin 14) :
    rawSwapMatrixColor leaf u v =
      ProfileDFourRowKindSymmetry.hostColorPerm
        (orderedMatrixColor leaf
          (ProfileDUUUFourSupportBlockTwoSwap61.restoredK15CoordinateSwap u)
          (ProfileDUUUFourSupportBlockTwoSwap61.restoredK15CoordinateSwap v)) := by
  rw [rawSwapMatrixColor, checkedColorSwap_eq_semantic,
    checkedCoordinateSwap_eq_semantic, checkedCoordinateSwap_eq_semantic]

/-! ## Allowed local relabellings -/

/-- Lexicographic `S₄`, matching the discovery quotient exactly. -/
def freeFourAction : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]]

theorem freeFourAction_bijective (action : Fin 24) :
    Function.Bijective (freeFourAction action) := by
  fin_cases action <;> decide

noncomputable def freeFourActionEquiv (action : Fin 24) :
    Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (freeFourAction action) (freeFourAction_bijective action)

abbrev FourFiveFiveCoordinates :=
  ProfileDFourSupportRestoredRootK15.FourFiveFiveCoordinates

def localCoordinateActionOnCoordinates
    (first second : SupportRepresentative)
    (free : Fin 24) (firstAction secondAction : Fin 10) :
    FourFiveFiveCoordinates → FourFiveFiveCoordinates
  | .inl (.inl p) => .inl (.inl (freeFourAction free p))
  | .inl (.inr p) => .inl (.inr (q2SupportAction first firstAction p))
  | .inr p => .inr (q2SupportAction second secondAction p)

def localCoordinateAction
    (first second : SupportRepresentative)
    (free : Fin 24) (firstAction secondAction : Fin 10)
    (i : Fin 14) : Fin 14 :=
  ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv
    (localCoordinateActionOnCoordinates first second free firstAction secondAction
      (ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm i))

noncomputable def localCoordinateEquiv
    (first second : SupportRepresentative)
    (free : Fin 24) (firstAction secondAction : Fin 10) :
    Equiv.Perm (Fin 14) :=
  ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm |>.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr (freeFourActionEquiv free)
        (q2SupportActionEquiv first firstAction))
      (q2SupportActionEquiv second secondAction)).trans
        ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv)

@[simp] theorem localCoordinateEquiv_apply
    (first second : SupportRepresentative)
    (free : Fin 24) (firstAction secondAction : Fin 10) (i : Fin 14) :
    localCoordinateEquiv first second free firstAction secondAction i =
      localCoordinateAction first second free firstAction secondAction i := by
  change ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv
      ((Equiv.sumCongr
        (Equiv.sumCongr (freeFourActionEquiv free)
          (q2SupportActionEquiv first firstAction))
        (q2SupportActionEquiv second secondAction))
        (ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm i)) =
    ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv
      (localCoordinateActionOnCoordinates first second free firstAction secondAction
        (ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm i))
  generalize ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm i = c
  rcases c with (left | secondPosition)
  · rcases left with (freePosition | firstPosition) <;> rfl
  · rfl

theorem localCoordinateAction_bijective
    (first second : SupportRepresentative)
    (free : Fin 24) (firstAction secondAction : Fin 10) :
    Function.Bijective
      (localCoordinateAction first second free firstAction secondAction) := by
  have hfun :
      (localCoordinateEquiv first second free firstAction secondAction :
        Fin 14 → Fin 14) =
        localCoordinateAction first second free firstAction secondAction := by
    funext i
    exact localCoordinateEquiv_apply first second free firstAction secondAction i
  rw [← hfun]
  exact (localCoordinateEquiv first second free firstAction secondAction).bijective

def witnessFree (leaf : OrderedLeaf) : Fin 24 :=
  Fin.ofNat 24 (ProfileDUUUFourSupportP15SwapData61.swapWitnessWord leaf)

def witnessFirst (leaf : OrderedLeaf) : Fin 10 :=
  Fin.ofNat 10
    (ProfileDUUUFourSupportP15SwapData61.swapWitnessWord leaf / 24)

def witnessSecond (leaf : OrderedLeaf) : Fin 10 :=
  Fin.ofNat 10
    (ProfileDUUUFourSupportP15SwapData61.swapWitnessWord leaf / (24 * 10))

/-- The local relabelling is attached to the target leaf, hence its two
support parameters use the swapped support order. -/
def swapWitnessCoordinate (leaf : OrderedLeaf) : Fin 14 → Fin 14 :=
  localCoordinateAction
    (ProfileDUUUFourSupportP15SwapData61.orderedFirst
      (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))
    (ProfileDUUUFourSupportP15SwapData61.orderedSecond
      (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))
    (witnessFree leaf) (witnessFirst leaf) (witnessSecond leaf)

theorem swapWitnessCoordinate_bijective (leaf : OrderedLeaf) :
    Function.Bijective (swapWitnessCoordinate leaf) := by
  exact localCoordinateAction_bijective _ _ _ _ _

/- The two support actions are not merely abstract five-point permutations:
the existing checked q=2 stabilizer theorem exhibits their extensions to
strong automorphisms of the ambient untwisted K15 template. -/
theorem firstWitnessAction_extends_strongly (leaf : OrderedLeaf) (p : Fin 5) :
    ProfileDUUUDegreeTenCatalogOrbits61.u15StabilizerEquiv .support7
        (q2VertexActionIndex
          (ProfileDUUUFourSupportP15SwapData61.orderedFirst
            (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))
          (witnessFirst leaf))
        ((support
          (ProfileDUUUFourSupportP15SwapData61.orderedFirst
            (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))).embedding p) =
      (support
        (ProfileDUUUFourSupportP15SwapData61.orderedFirst
          (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))).embedding
        (q2SupportAction
          (ProfileDUUUFourSupportP15SwapData61.orderedFirst
            (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))
          (witnessFirst leaf) p) := by
  exact q2Stabilizer_canonicalEmbedding _ _ _

theorem secondWitnessAction_extends_strongly (leaf : OrderedLeaf) (p : Fin 5) :
    ProfileDUUUDegreeTenCatalogOrbits61.u15StabilizerEquiv .support7
        (q2VertexActionIndex
          (ProfileDUUUFourSupportP15SwapData61.orderedSecond
            (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))
          (witnessSecond leaf))
        ((support
          (ProfileDUUUFourSupportP15SwapData61.orderedSecond
            (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))).embedding p) =
      (support
        (ProfileDUUUFourSupportP15SwapData61.orderedSecond
          (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))).embedding
        (q2SupportAction
          (ProfileDUUUFourSupportP15SwapData61.orderedSecond
            (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf))
          (witnessSecond leaf) p) := by
  exact q2Stabilizer_canonicalEmbedding _ _ _

/-! ## Checked involution and 189-seed coverage -/

def SwapLeafExact (leaf : OrderedLeaf) : Prop :=
  ProfileDUUUFourSupportP15SwapData61.orderedFirst
      (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf) =
    ProfileDUUUFourSupportP15SwapData61.orderedSecond leaf ∧
  ProfileDUUUFourSupportP15SwapData61.orderedSecond
      (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf) =
    ProfileDUUUFourSupportP15SwapData61.orderedFirst leaf ∧
  ∀ u v : Fin 14, u ≠ v →
    rawSwapMatrixColor leaf u v =
      orderedMatrixColor
        (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf)
        (swapWitnessCoordinate leaf u) (swapWitnessCoordinate leaf v)

instance (leaf : OrderedLeaf) : Decidable (SwapLeafExact leaf) := by
  unfold SwapLeafExact
  infer_instance

/-- Every stored lookup edge is the exact semantic matrix swap, modulo only
the local actions already admitted by the ordered quotient. -/
def chunk0 (i : Fin 62) : OrderedLeaf := ⟨i.val, by omega⟩
def chunk1 (i : Fin 62) : OrderedLeaf := ⟨62 + i.val, by omega⟩
def chunk2 (i : Fin 62) : OrderedLeaf := ⟨124 + i.val, by omega⟩
def chunk3 (i : Fin 62) : OrderedLeaf := ⟨186 + i.val, by omega⟩
def chunk4 (i : Fin 62) : OrderedLeaf := ⟨248 + i.val, by omega⟩
def chunk5 (i : Fin 62) : OrderedLeaf := ⟨310 + i.val, by omega⟩

theorem swapLeaf_exact_chunk0 (i : Fin 62) : SwapLeafExact (chunk0 i) := by
  fin_cases i <;> decide

theorem swapLeaf_exact_chunk1 (i : Fin 62) : SwapLeafExact (chunk1 i) := by
  fin_cases i <;> decide

theorem swapLeaf_exact_chunk2 (i : Fin 62) : SwapLeafExact (chunk2 i) := by
  fin_cases i <;> decide

theorem swapLeaf_exact_chunk3 (i : Fin 62) : SwapLeafExact (chunk3 i) := by
  fin_cases i <;> decide

theorem swapLeaf_exact_chunk4 (i : Fin 62) : SwapLeafExact (chunk4 i) := by
  fin_cases i <;> decide

theorem swapLeaf_exact_chunk5 (i : Fin 62) : SwapLeafExact (chunk5 i) := by
  fin_cases i <;> decide

theorem swapLeaf_exact (leaf : OrderedLeaf) : SwapLeafExact leaf := by
  by_cases h0 : leaf.val < 62
  · have heq : leaf = chunk0 ⟨leaf.val, h0⟩ := by
      apply Fin.ext
      simp [chunk0]
    rw [heq]
    exact swapLeaf_exact_chunk0 _
  by_cases h1 : leaf.val < 124
  · have hlow : 62 ≤ leaf.val := by omega
    let i : Fin 62 := ⟨leaf.val - 62, by omega⟩
    have heq : leaf = chunk1 i := by
      apply Fin.ext
      simp [chunk1, i]
      omega
    rw [heq]
    exact swapLeaf_exact_chunk1 _
  by_cases h2 : leaf.val < 186
  · have hlow : 124 ≤ leaf.val := by omega
    let i : Fin 62 := ⟨leaf.val - 124, by omega⟩
    have heq : leaf = chunk2 i := by
      apply Fin.ext
      simp [chunk2, i]
      omega
    rw [heq]
    exact swapLeaf_exact_chunk2 _
  by_cases h3 : leaf.val < 248
  · have hlow : 186 ≤ leaf.val := by omega
    let i : Fin 62 := ⟨leaf.val - 186, by omega⟩
    have heq : leaf = chunk3 i := by
      apply Fin.ext
      simp [chunk3, i]
      omega
    rw [heq]
    exact swapLeaf_exact_chunk3 _
  by_cases h4 : leaf.val < 310
  · have hlow : 248 ≤ leaf.val := by omega
    let i : Fin 62 := ⟨leaf.val - 248, by omega⟩
    have heq : leaf = chunk4 i := by
      apply Fin.ext
      simp [chunk4, i]
      omega
    rw [heq]
    exact swapLeaf_exact_chunk4 _
  · have hlow : 310 ≤ leaf.val := by omega
    let i : Fin 62 := ⟨leaf.val - 310, by omega⟩
    have heq : leaf = chunk5 i := by
      apply Fin.ext
      simp [chunk5, i]
      omega
    rw [heq]
    exact swapLeaf_exact_chunk5 _

theorem swapLeaf_involutive (leaf : OrderedLeaf) :
    ProfileDUUUFourSupportP15SwapData61.swapLeaf
      (ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf) = leaf := by
  fin_cases leaf <;> decide

theorem seedLeaf_injective :
    Function.Injective ProfileDUUUFourSupportP15SwapData61.seedLeaf := by
  decide

theorem orbitSeed_seedLeaf (seed : SwapSeed) :
    ProfileDUUUFourSupportP15SwapData61.orbitSeed
      (ProfileDUUUFourSupportP15SwapData61.seedLeaf seed) = seed := by
  fin_cases seed <;> decide

/-- The core 189-over-372 finite coverage statement. -/
theorem seed_covers_ordered_leaf (leaf : OrderedLeaf) :
    leaf = ProfileDUUUFourSupportP15SwapData61.seedLeaf
        (ProfileDUUUFourSupportP15SwapData61.orbitSeed leaf) ∨
      ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf =
        ProfileDUUUFourSupportP15SwapData61.seedLeaf
          (ProfileDUUUFourSupportP15SwapData61.orbitSeed leaf) := by
  fin_cases leaf <;> decide

/-- Coverage and exact matrix transport in one theorem, ready for a future
189-certificate assembly. -/
theorem exists_exact_seed_cover (leaf : OrderedLeaf) :
    ∃ seed : SwapSeed,
      (leaf = ProfileDUUUFourSupportP15SwapData61.seedLeaf seed ∨
        ProfileDUUUFourSupportP15SwapData61.swapLeaf leaf =
          ProfileDUUUFourSupportP15SwapData61.seedLeaf seed) ∧
      SwapLeafExact leaf := by
  exact ⟨ProfileDUUUFourSupportP15SwapData61.orbitSeed leaf,
    seed_covers_ordered_leaf leaf, swapLeaf_exact leaf⟩

#print axioms checkedCoordinateSwap_eq_semantic
#print axioms rawSwapMatrixColor_eq_semantic
#print axioms swapWitnessCoordinate_bijective
#print axioms firstWitnessAction_extends_strongly
#print axioms swapLeaf_exact
#print axioms swapLeaf_involutive
#print axioms seed_covers_ordered_leaf
#print axioms exists_exact_seed_cover

end ProfileDUUUFourSupportP15SwapFiniteCoverage61
end R4333
