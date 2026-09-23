import R4333Lean.ProfileDUUUDegreeTenSupportTransportUUU2P15
import R4333Lean.ProfileDUUUDegreeTenCatalogSemanticCompleteness61
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

/-!
# Semantic entrance to the UUU / block-two catalogue

After support normalization, the exact block-two host avoids host colour
three.  A fixed colour equivalence and the checked pair-specific coordinate
alignment convert it to the generic normalized catalogue convention, which
avoids colour one.  Generic semantic completeness then produces an actual
row of the 600-entry catalogue and transports it back to an exact block-two
branch.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogSemanticEntryUUU2P15

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogSemanticCompleteness61
open ProfileDUUUDegreeTenCatalogLeafBridgeUUU2P15
open ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
open ProfileDUUUDegreeTenSupportClassificationUUU2P15
open ProfileDUUUDegreeTenSupportTransportUUU2P15
open ProfileDUUUDegreeTenEndToEndSemanticUUU0P2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition

abbrev MatrixFiveVertex :=
  ProfileDHighOwnFiveRowSplit61.FiveVertex

def catalogToBlockTwoColorEquiv : Equiv.Perm (Fin 4) where
  toFun := catalogToBlockTwoColor
  invFun := ![0, 2, 3, 1]
  left_inv := by intro color; fin_cases color <;> decide
  right_inv := by intro color; fin_cases color <;> decide

noncomputable def alignedCatalogVertexEquiv
    (first second : SupportRepresentative) : Equiv.Perm (Fin 15) :=
  Equiv.ofBijective (alignedCatalogVertex first second)
    (alignedCatalogVertex_bijective first second)

theorem firstLocalAlignmentInverse_bijective
    (support : SupportRepresentative) :
    Function.Bijective (firstLocalAlignmentInverse support) := by
  cases support <;> decide

theorem secondLocalAlignmentInverse_bijective
    (support : SupportRepresentative) :
    Function.Bijective (secondLocalAlignmentInverse support) := by
  cases support <;> decide

@[simp] theorem alignedCatalogVertexEquiv_symm_blockZero
    (first second : SupportRepresentative) (position : Fin 5) :
    (alignedCatalogVertexEquiv first second).symm
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position := by
  apply (alignedCatalogVertexEquiv first second).injective
  rw [Equiv.apply_symm_apply]
  change ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position =
    alignedCatalogVertex first second
      (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position)
  cases first <;> cases second <;> fin_cases position <;> decide

@[simp] theorem alignedCatalogVertexEquiv_symm_blockOne
    (first second : SupportRepresentative) (position : Fin 5) :
    (alignedCatalogVertexEquiv first second).symm
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1
        (firstLocalAlignmentInverse first position) := by
  apply (alignedCatalogVertexEquiv first second).injective
  rw [Equiv.apply_symm_apply]
  change ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position =
    alignedCatalogVertex first second
      (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1
        (firstLocalAlignmentInverse first position))
  cases first <;> cases second <;> fin_cases position <;> decide

@[simp] theorem alignedCatalogVertexEquiv_symm_blockTwo
    (first second : SupportRepresentative) (position : Fin 5) :
    (alignedCatalogVertexEquiv first second).symm
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2
        (secondLocalAlignmentInverse second position) := by
  apply (alignedCatalogVertexEquiv first second).injective
  rw [Equiv.apply_symm_apply]
  change ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position =
    alignedCatalogVertex first second
      (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2
        (secondLocalAlignmentInverse second position))
  cases first <;> cases second <;> fin_cases position <;> decide

theorem alignedCatalogVertex_preserves_group
    (first second : SupportRepresentative) (vertex : Fin 15) :
    (alignedCatalogVertex first second vertex).val / 5 = vertex.val / 5 := by
  cases first <;> cases second <;> fin_cases vertex <;> decide

/-! ## The semantic host at block two -/

def exactHost
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) : EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring
    (totalColoring
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension)
    coordinates.vertex

theorem exactHost_noMono
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    NoMonochromaticTriangle (exactHost exact) := by
  exact noMono_pullback _ coordinates.vertex coordinates.vertex.injective
    (totalColoring_noMono
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension)

theorem selectedTotalVertex_ne_matrixVertex
    (coordinates : MatrixCoordinates 2) (i : Fin 15) :
    tailVertex
        (ProfileDTripleJoinReduction.blockVertex 2 SelectedPosition.val) ≠
      coordinates.vertex i := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero]
      intro h
      have := congrArg splitVertex h
      simp at this
    · rw [threeFiveEquiv_blockOne,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne]
      exact tailVertex_injective.ne
        (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
          2 0 (by decide) SelectedPosition.isLt (by
            have hp := (coordinates.first.embedding position).isLt
            change (coordinates.first.embedding position).val < 15 at hp
            exact hp))
  · rw [threeFiveEquiv_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo]
    exact tailVertex_injective.ne
      (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
        2 1 (by decide) SelectedPosition.isLt (by
          have hp := (coordinates.second.embedding position).isLt
          change (coordinates.second.embedding position).val < 15 at hp
          exact hp))

theorem selected_to_matrixVertex_ownColor
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) (i : Fin 15) :
    totalColoring
        exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
        (tailVertex
          (ProfileDTripleJoinReduction.blockVertex 2 SelectedPosition.val))
        (coordinates.vertex i) = 3 := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero]
      rw [(totalColoring
        exact.branch.toDegreeFlooredFiveExtension.toFiveExtension).color_symm,
        totalColoring_free_tail]
      change exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
          position
          (ProfileDTripleJoinReduction.blockVertex 2 SelectedPosition.val) = 3
      exact exact.branch.allFiveOwn position
    · rw [threeFiveEquiv_blockOne,
        ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne,
        totalColoring_tail_tail]
      apply (exact.firstSupportExact
        (coordinates.first.embedding position)).mp
      unfold OrderedFiveSupport.positions
      exact Finset.mem_image.mpr
        ⟨position, Finset.mem_univ _, rfl⟩
  · rw [threeFiveEquiv_blockTwo,
      ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo,
      totalColoring_tail_tail]
    apply (exact.secondSupportExact
      (coordinates.second.embedding position)).mp
    unfold OrderedFiveSupport.positions
    exact Finset.mem_image.mpr
      ⟨position, Finset.mem_univ _, rfl⟩

theorem exactHost_avoids_ownColor
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    ∀ u v, u ≠ v → exactHost exact u v ≠ 3 := by
  intro u v huv hcolor
  let selected := tailVertex
    (ProfileDTripleJoinReduction.blockVertex 2 SelectedPosition.val)
  apply totalColoring_noMono
    exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
    selected (coordinates.vertex u) (coordinates.vertex v)
  · exact ⟨selectedTotalVertex_ne_matrixVertex coordinates u,
      selectedTotalVertex_ne_matrixVertex coordinates v,
      coordinates.vertex.injective.ne huv⟩
  · exact ⟨
      (selected_to_matrixVertex_ownColor exact u).trans
        (selected_to_matrixVertex_ownColor exact v).symm,
      (selected_to_matrixVertex_ownColor exact v).trans hcolor.symm⟩

theorem exactHost_blockZero_internal
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix)
    (left right : MatrixFiveVertex) (hne : left ≠ right) :
    exactHost exact (blockVertex 0 left) (blockVertex 0 right) =
      decodeRemainingColor 2 (!canonicalCycleWord.coloring left right) := by
  change totalColoring
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
      ((coordinatesFor first second).vertex (blockVertex 0 left))
      ((coordinatesFor first second).vertex (blockVertex 0 right)) = _
  rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero,
    ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockZero,
    totalColoring_free_free, exact.branch.insideCanonical left right hne]

theorem exactHost_blockOne_internal
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix)
    (left right : MatrixFiveVertex) (hne : left ≠ right) :
    exactHost exact (blockVertex 1 left) (blockVertex 1 right) =
      SingleRootStarCNF.canonicalPalette 1
        (k15Template false
          ((coordinatesFor first second).first.embedding left)
          ((coordinatesFor first second).first.embedding right)) := by
  change totalColoring
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
      ((coordinatesFor first second).vertex (blockVertex 1 left))
      ((coordinatesFor first second).vertex (blockVertex 1 right)) = _
  rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne,
    ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockOne,
    totalColoring_tail_tail]
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      0 (by decide)
      ((coordinatesFor first second).first.embedding left)
      ((coordinatesFor first second).first.embedding right)
      ((coordinatesFor first second).first.embedding.injective.ne hne)
  have htwisted : Kind.uuu.twisted (0 : Fin 3) = false := by rfl
  rw [htwisted] at hedge
  exact hedge

theorem exactHost_blockTwo_internal
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix)
    (left right : MatrixFiveVertex) (hne : left ≠ right) :
    exactHost exact (blockVertex 2 left) (blockVertex 2 right) =
      SingleRootStarCNF.canonicalPalette 2
        (k15Template false
          ((coordinatesFor first second).second.embedding left)
          ((coordinatesFor first second).second.embedding right)) := by
  change totalColoring
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
      ((coordinatesFor first second).vertex (blockVertex 2 left))
      ((coordinatesFor first second).vertex (blockVertex 2 right)) = _
  rw [ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo,
    ProfileDUUUDegreeTenSupportTransportUUU2P15.matrixCoordinates_vertex_blockTwo,
    totalColoring_tail_tail]
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      1 (by decide)
      ((coordinatesFor first second).second.embedding left)
      ((coordinatesFor first second).second.embedding right)
      ((coordinatesFor first second).second.embedding.injective.ne hne)
  have htwisted : Kind.uuu.twisted (1 : Fin 3) = false := by rfl
  rw [htwisted] at hedge
  exact hedge

/-! ## Conversion to the generic catalogue convention -/

noncomputable def transformedExactHost
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix) :
    EdgeColoring (Fin 15) (Fin 4) :=
  mapEdgeColors
    (relabelVertices (exactHost exact)
      (alignedCatalogVertexEquiv first second).symm)
    catalogToBlockTwoColorEquiv.symm

theorem transformedExactHost_noMono
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix) :
    NoMonochromaticTriangle (transformedExactHost first second exact) := by
  exact noMono_mapEdgeColors _ _
    (noMono_relabelVertices _ _ (exactHost_noMono exact))

theorem transformedExactHost_avoids_catalogOwnColor
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix) :
    ∀ u v, u ≠ v → transformedExactHost first second exact u v ≠ 1 := by
  intro u v huv hcolor
  have hvertices :
      (alignedCatalogVertexEquiv first second).symm u ≠
        (alignedCatalogVertexEquiv first second).symm v :=
    (alignedCatalogVertexEquiv first second).symm.injective.ne huv
  apply exactHost_avoids_ownColor exact _ _ hvertices
  change catalogToBlockTwoColorEquiv.symm
      (exactHost exact
        ((alignedCatalogVertexEquiv first second).symm u)
        ((alignedCatalogVertexEquiv first second).symm v)) = 1 at hcolor
  have hmapped := congrArg catalogToBlockTwoColorEquiv hcolor
  have hhost :
      exactHost exact
          ((alignedCatalogVertexEquiv first second).symm u)
          ((alignedCatalogVertexEquiv first second).symm v) =
        catalogToBlockTwoColorEquiv 1 := by
    simpa only [Equiv.apply_symm_apply] using hmapped
  simpa [catalogToBlockTwoColorEquiv, catalogToBlockTwoColor] using hhost

theorem catalogRowZero_blockZero_internal
    (first second : SupportRepresentative)
    (left right : MatrixFiveVertex) (hne : left ≠ right) :
    catalogToBlockTwoColorEquiv.symm
        (decodeRemainingColor 2 (!canonicalCycleWord.coloring left right)) =
      catalogMatrixColor (catalogSupportKind first) 0
        (blockVertex 0 left) (blockVertex 0 right) := by
  cases first <;> cases second <;> fin_cases left <;> fin_cases right <;>
    simp_all [catalogToBlockTwoColorEquiv, catalogToBlockTwoColor] <;> decide

theorem catalogRowZero_blockOne_internal
    (first second : SupportRepresentative)
    (left right : MatrixFiveVertex) (hne : left ≠ right) :
    catalogToBlockTwoColorEquiv.symm
        (SingleRootStarCNF.canonicalPalette 1
          (k15Template false
            ((coordinatesFor first second).first.embedding
              (firstLocalAlignmentInverse first left))
            ((coordinatesFor first second).first.embedding
              (firstLocalAlignmentInverse first right)))) =
      catalogMatrixColor (catalogSupportKind first) 0
        (blockVertex 1 left) (blockVertex 1 right) := by
  cases first <;> cases second <;> fin_cases left <;> fin_cases right <;>
    simp_all [catalogToBlockTwoColorEquiv, catalogToBlockTwoColor] <;> decide

theorem catalogRowZero_blockTwo_internal
    (first second : SupportRepresentative)
    (left right : MatrixFiveVertex) (hne : left ≠ right) :
    catalogToBlockTwoColorEquiv.symm
        (SingleRootStarCNF.canonicalPalette 2
          (k15Template false
            ((coordinatesFor first second).second.embedding
              (secondLocalAlignmentInverse second left))
            ((coordinatesFor first second).second.embedding
              (secondLocalAlignmentInverse second right)))) =
      catalogMatrixColor (catalogSupportKind first) 0
        (blockVertex 2 left) (blockVertex 2 right) := by
  cases first <;> cases second <;> fin_cases left <;> fin_cases right <;>
    simp_all [catalogToBlockTwoColorEquiv, catalogToBlockTwoColor] <;> decide

theorem transformedExactHost_hasCanonicalInternalBlocks
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix) :
    HasCanonicalInternalBlocks (catalogSupportKind first)
      (transformedExactHost first second exact) := by
  intro group left right hne
  fin_cases group
  · change catalogToBlockTwoColorEquiv.symm
      (exactHost exact
        ((alignedCatalogVertexEquiv first second).symm (blockVertex 0 left))
        ((alignedCatalogVertexEquiv first second).symm (blockVertex 0 right))) = _
    rw [alignedCatalogVertexEquiv_symm_blockZero,
      alignedCatalogVertexEquiv_symm_blockZero,
      exactHost_blockZero_internal first second exact left right hne]
    exact catalogRowZero_blockZero_internal first second left right hne
  · have hne' : firstLocalAlignmentInverse first left ≠
        firstLocalAlignmentInverse first right :=
      (firstLocalAlignmentInverse_bijective first).1.ne hne
    change catalogToBlockTwoColorEquiv.symm
      (exactHost exact
        ((alignedCatalogVertexEquiv first second).symm (blockVertex 1 left))
        ((alignedCatalogVertexEquiv first second).symm (blockVertex 1 right))) = _
    rw [alignedCatalogVertexEquiv_symm_blockOne,
      alignedCatalogVertexEquiv_symm_blockOne,
      exactHost_blockOne_internal first second exact _ _ hne']
    exact catalogRowZero_blockOne_internal first second left right hne
  · have hne' : secondLocalAlignmentInverse second left ≠
        secondLocalAlignmentInverse second right :=
      (secondLocalAlignmentInverse_bijective second).1.ne hne
    change catalogToBlockTwoColorEquiv.symm
      (exactHost exact
        ((alignedCatalogVertexEquiv first second).symm (blockVertex 2 left))
        ((alignedCatalogVertexEquiv first second).symm (blockVertex 2 right))) = _
    rw [alignedCatalogVertexEquiv_symm_blockTwo,
      alignedCatalogVertexEquiv_symm_blockTwo,
      exactHost_blockTwo_internal first second exact _ _ hne']
    exact catalogRowZero_blockTwo_internal first second left right hne

/-! ## Pulling a generic catalogue row back to block-two coordinates -/

noncomputable def blockTwoCatalogMatrix
    (first second : SupportRepresentative) (row : Fin 600) :
    EdgeColoring (Fin 15) (Fin 4) :=
  mapEdgeColors
    (relabelVertices
      (catalogEdgeColoring (catalogSupportKind first) row)
      (alignedCatalogVertexEquiv first second))
    catalogToBlockTwoColorEquiv

theorem catalogEquation_on_blockTwo_cross_indices
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix)
    (row : Fin 600)
    (hcatalog : ∀ leftBlock rightBlock : Fin 3,
      leftBlock ≠ rightBlock → ∀ left right : Fin 5,
        transformedExactHost first second exact
            (blockVertex leftBlock left) (blockVertex rightBlock right) =
          catalogMatrixColor (catalogSupportKind first) row
            (blockVertex leftBlock left) (blockVertex rightBlock right))
    (left right : Fin 15) (hgroups : left.val / 5 ≠ right.val / 5) :
    exactHost exact left right = blockTwoCatalogMatrix first second row left right := by
  have hgeneric := catalogEquation_on_cross_indices
    (catalogSupportKind first) (transformedExactHost first second exact) row
    hcatalog
    (alignedCatalogVertex first second left)
    (alignedCatalogVertex first second right) (by
      simpa [alignedCatalogVertex_preserves_group] using hgroups)
  have hgeneric' :
      catalogToBlockTwoColorEquiv.symm (exactHost exact left right) =
        catalogMatrixColor (catalogSupportKind first) row
          (alignedCatalogVertex first second left)
          (alignedCatalogVertex first second right) := by
    simpa [transformedExactHost, alignedCatalogVertexEquiv] using hgeneric
  have hmapped := congrArg catalogToBlockTwoColorEquiv hgeneric'
  have hclean :
      exactHost exact left right =
        catalogToBlockTwoColorEquiv
          (catalogMatrixColor (catalogSupportKind first) row
            (alignedCatalogVertex first second left)
            (alignedCatalogVertex first second right)) := by
    simpa only [Equiv.apply_symm_apply] using hmapped
  change exactHost exact left right =
    catalogToBlockTwoColorEquiv
      (catalogMatrixColor (catalogSupportKind first) row
        (alignedCatalogVertex first second left)
        (alignedCatalogVertex first second right))
  exact hclean

noncomputable def exactBranchWithCatalogMatrix
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix)
    (row : Fin 600)
    (hcatalog : ∀ left right : Fin 15,
      left.val / 5 ≠ right.val / 5 →
        exactHost exact left right =
          blockTwoCatalogMatrix first second row left right) :
    ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second)
      (blockTwoCatalogMatrix first second row) where
  branch := exact.branch
  tailOwnDegreeTen := exact.tailOwnDegreeTen
  firstSupportExact := exact.firstSupportExact
  secondSupportExact := exact.secondSupportExact
  matrixExact := by
    intro left right hgroups
    exact hcatalog left right hgroups

theorem exists_catalogExactBranch_of_normalized
    (first second : SupportRepresentative)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor first second) matrix) :
    ∃ row : Fin 600,
      Nonempty (ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
        (coordinatesFor first second)
        (blockTwoCatalogMatrix first second row)) := by
  obtain ⟨row, hcatalog⟩ :=
    exists_catalogMatrix_of_normalizedHost (catalogSupportKind first)
      (transformedExactHost first second exact)
      (transformedExactHost_noMono first second exact)
      (transformedExactHost_avoids_catalogOwnColor first second exact)
      (transformedExactHost_hasCanonicalInternalBlocks first second exact)
  refine ⟨row, ⟨exactBranchWithCatalogMatrix first second exact row ?_⟩⟩
  intro left right hgroups
  exact catalogEquation_on_blockTwo_cross_indices first second exact row
    hcatalog left right hgroups

def pairOfRepresentatives :
    SupportRepresentative → SupportRepresentative → Fin 9
  | .s0, .s0 => 0
  | .s0, .s1 => 1
  | .s0, .s4 => 2
  | .s1, .s0 => 3
  | .s1, .s1 => 4
  | .s1, .s4 => 5
  | .s4, .s0 => 6
  | .s4, .s1 => 7
  | .s4, .s4 => 8

@[simp] theorem pairFirst_pairOfRepresentatives
    (first second : SupportRepresentative) :
    pairFirst (pairOfRepresentatives first second) = first := by
  cases first <;> cases second <;> rfl

@[simp] theorem pairSecond_pairOfRepresentatives
    (first second : SupportRepresentative) :
    pairSecond (pairOfRepresentatives first second) = second := by
  cases first <;> cases second <;> rfl

/-- Full semantic entrance: every arbitrary exact branch transports to an
actual row of one of the nine block-two catalogue pairs. -/
theorem exists_catalogExactBranch_of_exact
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    ∃ pair : Fin 9, ∃ row : Fin 600,
      Nonempty (ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
        (coordinatesFor (pairFirst pair) (pairSecond pair))
        (blockTwoCatalogMatrix (pairFirst pair) (pairSecond pair) row)) := by
  obtain ⟨firstIndex, hfirst⟩ := exists_firstSupportIndex exact
  obtain ⟨secondIndex, hsecond⟩ := exists_secondSupportIndex exact
  let first := normalizedSupportRepresentative firstIndex
  let second := normalizedSupportRepresentative secondIndex
  let normalized := normalizeExactDegreeTenSupports exact firstIndex secondIndex
    hfirst hsecond
  obtain ⟨row, ⟨catalogExact⟩⟩ :=
    exists_catalogExactBranch_of_normalized first second normalized
  refine ⟨pairOfRepresentatives first second, row, ?_⟩
  refine ⟨?_⟩
  simpa using catalogExact

#print axioms transformedExactHost_hasCanonicalInternalBlocks
#print axioms exists_catalogExactBranch_of_normalized
#print axioms exists_catalogExactBranch_of_exact

end ProfileDUUUDegreeTenCatalogSemanticEntryUUU2P15
end R4333
