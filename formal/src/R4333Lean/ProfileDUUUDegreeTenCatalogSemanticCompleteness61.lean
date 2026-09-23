import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCertificate61
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateCertificate61

/-!
# Semantic completeness of the normalized UUU degree-ten catalogue

This is the bridge from an arbitrary triangle-free four-colour K15 host with
the normalized three internal five-cycles to the explicit 600-row catalogue.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogSemanticCompleteness61

open SingleRootStarCNF
open CriticalK15PartitionClassification
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogCompletenessData61
open ProfileDUUUDegreeTenCatalogLocalMaps61
open ProfileDUUUDegreeTenCatalogCandidateEquation61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def matrixGroupLabels (group : Fin 3) : Finset (Fin 15) :=
  Finset.univ.image (blockVertex group)

theorem blockVertex_fixed_injective (group : Fin 3) :
    Function.Injective (blockVertex group) := by
  fin_cases group <;> decide

theorem blockVertex_ne_of_group_ne
    {leftBlock rightBlock : Fin 3} (hblocks : leftBlock ≠ rightBlock)
    (left right : Fin 5) :
    blockVertex leftBlock left ≠ blockVertex rightBlock right := by
  fin_cases leftBlock <;> fin_cases rightBlock <;> simp_all <;> decide +revert

@[simp] theorem matrixGroupLabels_card (group : Fin 3) :
    (matrixGroupLabels group).card = 5 := by
  calc
    (matrixGroupLabels group).card =
        (Finset.univ : Finset (Fin 5)).card := by
      exact Finset.card_image_of_injective _
        (blockVertex_fixed_injective group)
    _ = 5 := by simp

theorem matrixGroupLabels_disjoint
    {left right : Fin 3} (hne : left ≠ right) :
    Disjoint (matrixGroupLabels left) (matrixGroupLabels right) := by
  fin_cases left <;> fin_cases right <;> simp_all <;> decide +revert

theorem matrixGroupLabels_cover :
    (matrixGroupLabels 0 ∪ matrixGroupLabels 1) ∪ matrixGroupLabels 2 =
      (Finset.univ : Finset (Fin 15)) := by
  decide

def HasCanonicalInternalBlocks (kind : SupportKind)
    (c : EdgeColoring (Fin 15) (Fin 4)) : Prop :=
  ∀ group : Fin 3, ∀ left right : Fin 5, left ≠ right →
    c (blockVertex group left) (blockVertex group right) =
      catalogMatrixColor kind 0
        (blockVertex group left) (blockVertex group right)

theorem catalogRowZero_internal_avoids_groupColor
    (kind : SupportKind) (group : Fin 3)
    (left right : Fin 5) (hne : left ≠ right) :
    catalogMatrixColor kind 0
        (blockVertex group left) (blockVertex group right) ≠
      canonicalPalette 1 group := by
  cases kind <;> fin_cases group <;> fin_cases left <;>
    fin_cases right <;> simp_all <;> decide

theorem matrixGroupLabels_independent
    (kind : SupportKind) (c : EdgeColoring (Fin 15) (Fin 4))
    (havoids : ∀ u v, u ≠ v → c u v ≠ 1)
    (hinside : HasCanonicalInternalBlocks kind c)
    (group : Fin 3) :
    IsColorIndependentSet (decodeNonBlockColoring 1 c) group
      (matrixGroupLabels group) := by
  intro x hx y hy hxy hcolor
  rw [matrixGroupLabels, Finset.mem_image] at hx hy
  obtain ⟨left, -, rfl⟩ := hx
  obtain ⟨right, -, rfl⟩ := hy
  have hlr : left ≠ right := by
    intro h
    subst right
    exact hxy rfl
  apply catalogRowZero_internal_avoids_groupColor kind group left right hlr
  calc
    catalogMatrixColor kind 0
        (blockVertex group left) (blockVertex group right) =
        c (blockVertex group left) (blockVertex group right) :=
      (hinside group left right hlr).symm
    _ = canonicalPalette 1
          (decodeNonBlockColoring 1 c
            (blockVertex group left) (blockVertex group right)) :=
      (canonicalPalette_decodeNonBlockColor 1
        (c (blockVertex group left) (blockVertex group right))
        (havoids _ _ hxy)).symm
    _ = canonicalPalette 1 group := congrArg (canonicalPalette 1) hcolor

theorem catalogMatrixColor_symm
    (kind : SupportKind) (i : Fin 600) (left right : Fin 15) :
    catalogMatrixColor kind i left right =
      catalogMatrixColor kind i right left := by
  simp [catalogMatrixColor, catalogEdgeIndex, min_comm, max_comm]

theorem exists_partition_normalization
    (kind : SupportKind) (c : EdgeColoring (Fin 15) (Fin 4))
    (hc : NoMonochromaticTriangle c)
    (havoids : ∀ u v, u ≠ v → c u v ≠ 1)
    (hinside : HasCanonicalInternalBlocks kind c) :
    ∃ twisted : Bool,
      ∃ e : WeakColorEquiv (decodeNonBlockColoring 1 c)
          (k15Template twisted),
        e.colors = Equiv.refl ThreeColor ∧
          ∀ group : Fin 3,
            (matrixGroupLabels group).image e.vertex =
              canonicalPart twisted group := by
  have hdecoded :
      NoMonochromaticTriangle (decodeNonBlockColoring 1 c) :=
    decodeNonBlockColoring_noMono 1 c hc havoids
  obtain ⟨twisted, e, hcolors, hpartition⟩ :=
    exists_partition_normalization_of_good
      (decodeNonBlockColoring 1 c) hdecoded
  have hparts := hpartition
    (matrixGroupLabels 0) (matrixGroupLabels 1) (matrixGroupLabels 2)
    (matrixGroupLabels_card 0) (matrixGroupLabels_card 1)
    (matrixGroupLabels_card 2)
    (matrixGroupLabels_independent kind c havoids hinside 0)
    (matrixGroupLabels_independent kind c havoids hinside 1)
    (matrixGroupLabels_independent kind c havoids hinside 2)
    (matrixGroupLabels_disjoint (by decide))
    (matrixGroupLabels_disjoint (by decide))
    (matrixGroupLabels_disjoint (by decide)) matrixGroupLabels_cover
  refine ⟨twisted, e, hcolors, ?_⟩
  intro group
  fin_cases group
  · exact hparts.1
  · exact hparts.2.1
  · exact hparts.2.2

def normalizedLocalMap (twisted : Bool) (vertex : Fin 15 ≃ Fin 15)
    (group : Fin 3) (position : Fin 5) : Fin 5 :=
  canonicalPartPosition twisted group
    (vertex (blockVertex group position))

theorem normalizedLocalMap_vertex
    (twisted : Bool) (vertex : Fin 15 ≃ Fin 15) (group : Fin 3)
    (himage : (matrixGroupLabels group).image vertex =
      canonicalPart twisted group)
    (position : Fin 5) :
    canonicalPartVertex twisted group
        (normalizedLocalMap twisted vertex group position) =
      vertex (blockVertex group position) := by
  apply canonicalPartVertex_position_of_mem
  rw [← himage]
  apply Finset.mem_image.mpr
  refine ⟨blockVertex group position, ?_, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨position, Finset.mem_univ _, rfl⟩

theorem normalizedLocalMap_bijective
    (twisted : Bool) (vertex : Fin 15 ≃ Fin 15) (group : Fin 3)
    (himage : (matrixGroupLabels group).image vertex =
      canonicalPart twisted group) :
    Function.Bijective (normalizedLocalMap twisted vertex group) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro left right heq
    apply blockVertex_fixed_injective group
    apply vertex.injective
    calc
      vertex (blockVertex group left) =
          canonicalPartVertex twisted group
            (normalizedLocalMap twisted vertex group left) :=
        (normalizedLocalMap_vertex twisted vertex group himage left).symm
      _ = canonicalPartVertex twisted group
            (normalizedLocalMap twisted vertex group right) :=
        congrArg (canonicalPartVertex twisted group) heq
      _ = vertex (blockVertex group right) :=
        normalizedLocalMap_vertex twisted vertex group himage right
  · simp

theorem normalizedLocalMap_compatible
    (kind : SupportKind) (c : EdgeColoring (Fin 15) (Fin 4))
    (havoids : ∀ u v, u ≠ v → c u v ≠ 1)
    (hinside : HasCanonicalInternalBlocks kind c)
    (twisted : Bool)
    (e : WeakColorEquiv (decodeNonBlockColoring 1 c)
      (k15Template twisted))
    (hcolors : e.colors = Equiv.refl ThreeColor)
    (group : Fin 3)
    (himage : (matrixGroupLabels group).image e.vertex =
      canonicalPart twisted group) :
    IsCompatibleMap kind twisted group
      (normalizedLocalMap twisted e.vertex group) := by
  unfold IsCompatibleMap
  constructor
  · exact normalizedLocalMap_bijective twisted e.vertex group himage
  · intro left right hne
    rw [normalizedLocalMap_vertex twisted e.vertex group himage left,
      normalizedLocalMap_vertex twisted e.vertex group himage right]
    have hvertices :
        blockVertex group left ≠ blockVertex group right :=
      (blockVertex_fixed_injective group).ne hne
    have hemap := e.map_color
      (blockVertex group left) (blockVertex group right) hvertices
    calc
      canonicalPalette 1
          (k15Template twisted
            (e.vertex (blockVertex group left))
            (e.vertex (blockVertex group right))) =
          canonicalPalette 1
            (e.colors
              (decodeNonBlockColoring 1 c
                (blockVertex group left) (blockVertex group right))) :=
        (congrArg (canonicalPalette 1) hemap).symm
      _ = canonicalPalette 1
            (decodeNonBlockColoring 1 c
              (blockVertex group left) (blockVertex group right)) := by
        rw [hcolors]
        rfl
      _ = c (blockVertex group left) (blockVertex group right) :=
        canonicalPalette_decodeNonBlockColor 1
          (c (blockVertex group left) (blockVertex group right))
          (havoids _ _ hvertices)
      _ = catalogMatrixColor kind 0
            (blockVertex group left) (blockVertex group right) :=
        hinside group left right hne

@[simp] theorem candidateTemplateVertex_blockVertex
    (kind : SupportKind) (twisted : Bool) (a0 a1 a2 : Fin 10)
    (group : Fin 3) (position : Fin 5) :
    candidateTemplateVertex kind twisted a0 a1 a2
        (blockVertex group position) =
      canonicalPartVertex twisted group
        (selectedCompatibleMap kind twisted a0 a1 a2 group position) := by
  fin_cases group <;> fin_cases position <;> rfl

/-- Any normalized semantic K15 host is one of the explicit 600 catalogue
rows.  The witness is an actual row index, and the conclusion covers both
orientations of every cross-block edge. -/
theorem exists_catalogMatrix_of_normalizedHost
    (kind : SupportKind) (c : EdgeColoring (Fin 15) (Fin 4))
    (hc : NoMonochromaticTriangle c)
    (havoids : ∀ u v, u ≠ v → c u v ≠ 1)
    (hinside : HasCanonicalInternalBlocks kind c) :
    ∃ i : Fin 600,
      ∀ leftBlock rightBlock : Fin 3, leftBlock ≠ rightBlock →
        ∀ left right : Fin 5,
          c (blockVertex leftBlock left) (blockVertex rightBlock right) =
            catalogMatrixColor kind i
              (blockVertex leftBlock left) (blockVertex rightBlock right) := by
  obtain ⟨twisted, e, hcolors, himages⟩ :=
    exists_partition_normalization kind c hc havoids hinside
  have hcompatible0 := normalizedLocalMap_compatible kind c havoids hinside
    twisted e hcolors 0 (himages 0)
  have hcompatible1 := normalizedLocalMap_compatible kind c havoids hinside
    twisted e hcolors 1 (himages 1)
  have hcompatible2 := normalizedLocalMap_compatible kind c havoids hinside
    twisted e hcolors 2 (himages 2)
  obtain ⟨a0, ha0⟩ := compatibleMap_complete kind twisted 0
    (normalizedLocalMap twisted e.vertex 0) hcompatible0
  obtain ⟨a1, ha1⟩ := compatibleMap_complete kind twisted 1
    (normalizedLocalMap twisted e.vertex 1) hcompatible1
  obtain ⟨a2, ha2⟩ := compatibleMap_complete kind twisted 2
    (normalizedLocalMap twisted e.vertex 2) hcompatible2
  have hcandidateVertex : ∀ group : Fin 3, ∀ position : Fin 5,
      candidateTemplateVertex kind twisted a0 a1 a2
          (blockVertex group position) =
        e.vertex (blockVertex group position) := by
    intro group position
    fin_cases group
    · rw [candidateTemplateVertex_blockVertex]
      change canonicalPartVertex twisted 0
          (compatibleMap kind twisted 0 a0 position) =
        e.vertex (blockVertex 0 position)
      rw [← ha0 position]
      exact normalizedLocalMap_vertex twisted e.vertex 0
        (himages 0) position
    · rw [candidateTemplateVertex_blockVertex]
      change canonicalPartVertex twisted 1
          (compatibleMap kind twisted 1 a1 position) =
        e.vertex (blockVertex 1 position)
      rw [← ha1 position]
      exact normalizedLocalMap_vertex twisted e.vertex 1
        (himages 1) position
    · rw [candidateTemplateVertex_blockVertex]
      change canonicalPartVertex twisted 2
          (compatibleMap kind twisted 2 a2 position) =
        e.vertex (blockVertex 2 position)
      rw [← ha2 position]
      exact normalizedLocalMap_vertex twisted e.vertex 2
        (himages 2) position
  have hhostCandidate :
      ∀ leftBlock rightBlock : Fin 3,
        leftBlock.val < rightBlock.val →
        ∀ left right : Fin 5,
          c (blockVertex leftBlock left) (blockVertex rightBlock right) =
            candidateMatrixColor kind twisted a0 a1 a2
              (blockVertex leftBlock left) (blockVertex rightBlock right) := by
    intro leftBlock rightBlock hlt left right
    have hblocks : leftBlock ≠ rightBlock := by
      intro heq
      subst rightBlock
      omega
    have hvertices := blockVertex_ne_of_group_ne hblocks left right
    have hemap := e.map_color
      (blockVertex leftBlock left) (blockVertex rightBlock right) hvertices
    calc
      c (blockVertex leftBlock left) (blockVertex rightBlock right) =
          canonicalPalette 1
            (decodeNonBlockColoring 1 c
              (blockVertex leftBlock left) (blockVertex rightBlock right)) :=
        (canonicalPalette_decodeNonBlockColor 1
          (c (blockVertex leftBlock left) (blockVertex rightBlock right))
          (havoids _ _ hvertices)).symm
      _ = canonicalPalette 1
            (e.colors
              (decodeNonBlockColoring 1 c
                (blockVertex leftBlock left)
                (blockVertex rightBlock right))) := by
        rw [hcolors]
        rfl
      _ = canonicalPalette 1
            (k15Template twisted
              (e.vertex (blockVertex leftBlock left))
              (e.vertex (blockVertex rightBlock right))) :=
        congrArg (canonicalPalette 1) hemap
      _ = candidateMatrixColor kind twisted a0 a1 a2
            (blockVertex leftBlock left) (blockVertex rightBlock right) := by
        rw [← hcandidateVertex leftBlock left,
          ← hcandidateVertex rightBlock right]
        rfl
  let index := candidateCatalogIndex kind twisted a0 a1 a2
  have hordered :
      ∀ leftBlock rightBlock : Fin 3,
        leftBlock.val < rightBlock.val →
        ∀ left right : Fin 5,
          c (blockVertex leftBlock left) (blockVertex rightBlock right) =
            catalogMatrixColor kind index
              (blockVertex leftBlock left) (blockVertex rightBlock right) := by
    intro leftBlock rightBlock hlt left right
    exact (hhostCandidate leftBlock rightBlock hlt left right).trans
      (candidateCatalogEquation_selected kind twisted a0 a1 a2
        leftBlock rightBlock hlt left right)
  refine ⟨index, ?_⟩
  intro leftBlock rightBlock hblocks left right
  by_cases hlt : leftBlock.val < rightBlock.val
  · exact hordered leftBlock rightBlock hlt left right
  · have hvalues : leftBlock.val ≠ rightBlock.val := by
      intro heq
      exact hblocks (Fin.ext heq)
    have hreverse : rightBlock.val < leftBlock.val := by omega
    calc
      c (blockVertex leftBlock left) (blockVertex rightBlock right) =
          c (blockVertex rightBlock right) (blockVertex leftBlock left) :=
        c.color_symm _ _
      _ = catalogMatrixColor kind index
            (blockVertex rightBlock right) (blockVertex leftBlock left) :=
        hordered rightBlock leftBlock hreverse right left
      _ = catalogMatrixColor kind index
            (blockVertex leftBlock left) (blockVertex rightBlock right) :=
        catalogMatrixColor_symm kind index _ _

#print axioms matrixGroupLabels_independent
#print axioms catalogMatrixColor_symm
#print axioms exists_partition_normalization
#print axioms normalizedLocalMap_bijective
#print axioms normalizedLocalMap_compatible
#print axioms exists_catalogMatrix_of_normalizedHost

end ProfileDUUUDegreeTenCatalogSemanticCompleteness61
end R4333
