import R4333Lean.FourRowFreeVertexSymmetry

/-!
# Exact free-vertex orbits of root-forbidden triangle-free K4 colourings

The six coordinates are ordered as
`01, 02, 03, 12, 13, 23`.  Host colours remain fixed.  Exhaustive finite
checking shows that the 450 root-forbidden triangle-free words split into
exactly 36 orbits under the 24 vertex permutations of `Fin 4`.
-/

namespace R4333
namespace RootForbiddenK4FreeVertexOrbits

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The six unordered-edge colours of a labelled K4, in lexicographic edge
order `01, 02, 03, 12, 13, 23`. -/
@[ext] structure InsideWord where
  e01 : Fin 4
  e02 : Fin 4
  e03 : Fin 4
  e12 : Fin 4
  e13 : Fin 4
  e23 : Fin 4
  deriving DecidableEq, Fintype, Repr

/-- Interpret a six-edge word as a symmetric colouring.  Diagonal values are
irrelevant and are fixed to zero. -/
def InsideWord.coloring (w : InsideWord) : EdgeColoring (Fin 4) (Fin 4) where
  color a b := ![
    ![0, w.e01, w.e02, w.e03],
    ![w.e01, 0, w.e12, w.e13],
    ![w.e02, w.e12, 0, w.e23],
    ![w.e03, w.e13, w.e23, 0]
  ] a b
  color_symm := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl

/-- Read the six lexicographic edges from an arbitrary K4 colouring. -/
def InsideWord.ofColoring (c : EdgeColoring (Fin 4) (Fin 4)) : InsideWord :=
  ⟨c 0 1, c 0 2, c 0 3, c 1 2, c 1 3, c 2 3⟩

@[simp] theorem InsideWord.ofColoring_coloring (w : InsideWord) :
    InsideWord.ofColoring w.coloring = w := by
  cases w
  rfl

theorem InsideWord.coloring_ofColoring_offDiagonal
    (c : EdgeColoring (Fin 4) (Fin 4)) (a b : Fin 4) (hab : a ≠ b) :
    (InsideWord.ofColoring c).coloring a b = c a b := by
  fin_cases a <;> fin_cases b <;>
    simp [InsideWord.ofColoring, InsideWord.coloring] at hab ⊢ <;>
    exact c.color_symm _ _

/-- Pull a word back along a permutation of the four vertex labels. -/
def InsideWord.relabel (w : InsideWord) (σ : Equiv.Perm (Fin 4)) :
    InsideWord :=
  InsideWord.ofColoring (pullbackColoring w.coloring σ)

theorem InsideWord.ofColoring_pullback
    (c : EdgeColoring (Fin 4) (Fin 4)) (σ : Equiv.Perm (Fin 4)) :
    InsideWord.ofColoring (pullbackColoring c σ) =
      (InsideWord.ofColoring c).relabel σ := by
  apply InsideWord.ext <;>
    simp only [InsideWord.relabel, InsideWord.ofColoring,
      pullbackColoring]
  all_goals
    symm
    apply InsideWord.coloring_ofColoring_offDiagonal
    exact σ.injective.ne (by decide)

/-- Explicit decidable form of root-forbiddenness and the four nonmonochromatic
triangle conditions. -/
def InsideWord.Good (w : InsideWord) : Prop :=
  w.e01 ≠ 0 ∧ w.e02 ≠ 0 ∧ w.e03 ≠ 0 ∧
  w.e12 ≠ 0 ∧ w.e13 ≠ 0 ∧ w.e23 ≠ 0 ∧
  ¬(w.e01 = w.e02 ∧ w.e02 = w.e12) ∧
  ¬(w.e01 = w.e03 ∧ w.e03 = w.e13) ∧
  ¬(w.e02 = w.e03 ∧ w.e03 = w.e23) ∧
  ¬(w.e12 = w.e13 ∧ w.e13 = w.e23)

instance (w : InsideWord) : Decidable w.Good := by
  unfold InsideWord.Good
  infer_instance

theorem InsideWord.good_of_rootForbidden_noMono
    (c : EdgeColoring (Fin 4) (Fin 4))
    (hroot : ∀ a b, a ≠ b → c a b ≠ 0)
    (hnoMono : NoMonochromaticTriangle c) :
    (InsideWord.ofColoring c).Good := by
  refine ⟨hroot 0 1 (by decide), hroot 0 2 (by decide),
    hroot 0 3 (by decide), hroot 1 2 (by decide),
    hroot 1 3 (by decide), hroot 2 3 (by decide), ?_, ?_, ?_, ?_⟩
  · exact fun h => hnoMono 0 1 2 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 0 1 3 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 0 2 3 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 1 2 3 (by simp [PairwiseDistinct]) h

/-- One concrete representative of each free-vertex orbit.  Colours are not
permuted. -/
def canonicalRepresentatives : List InsideWord :=
  [ ⟨1, 1, 1, 2, 2, 3⟩
  , ⟨1, 1, 1, 2, 3, 3⟩
  , ⟨1, 1, 2, 2, 1, 1⟩
  , ⟨1, 1, 2, 2, 1, 2⟩
  , ⟨1, 1, 2, 2, 1, 3⟩
  , ⟨1, 1, 2, 2, 2, 3⟩
  , ⟨1, 1, 2, 2, 3, 3⟩
  , ⟨1, 1, 2, 3, 1, 1⟩
  , ⟨1, 1, 2, 3, 1, 2⟩
  , ⟨1, 1, 2, 3, 1, 3⟩
  , ⟨1, 1, 2, 3, 2, 2⟩
  , ⟨1, 1, 2, 3, 2, 3⟩
  , ⟨1, 1, 3, 2, 2, 3⟩
  , ⟨1, 1, 3, 2, 3, 3⟩
  , ⟨1, 1, 3, 3, 1, 1⟩
  , ⟨1, 1, 3, 3, 1, 2⟩
  , ⟨1, 1, 3, 3, 1, 3⟩
  , ⟨1, 1, 3, 3, 2, 2⟩
  , ⟨1, 1, 3, 3, 2, 3⟩
  , ⟨1, 2, 2, 2, 2, 1⟩
  , ⟨1, 2, 2, 2, 2, 3⟩
  , ⟨1, 2, 2, 2, 3, 1⟩
  , ⟨1, 2, 2, 2, 3, 3⟩
  , ⟨1, 2, 2, 3, 3, 1⟩
  , ⟨1, 2, 3, 2, 3, 2⟩
  , ⟨1, 2, 3, 2, 3, 3⟩
  , ⟨1, 2, 3, 3, 2, 1⟩
  , ⟨1, 2, 3, 3, 2, 2⟩
  , ⟨1, 2, 3, 3, 2, 3⟩
  , ⟨1, 2, 3, 3, 3, 1⟩
  , ⟨1, 2, 3, 3, 3, 2⟩
  , ⟨1, 3, 3, 3, 3, 1⟩
  , ⟨1, 3, 3, 3, 3, 2⟩
  , ⟨2, 2, 3, 3, 2, 2⟩
  , ⟨2, 2, 3, 3, 2, 3⟩
  , ⟨2, 3, 3, 3, 3, 2⟩ ]

theorem canonicalRepresentatives_length :
    canonicalRepresentatives.length = 36 := by decide

theorem canonicalRepresentatives_nodup :
    canonicalRepresentatives.Nodup := by decide

theorem canonicalRepresentatives_good :
    ∀ w ∈ canonicalRepresentatives, w.Good := by decide

/-- A concrete duplicate-free enumeration of all 24 vertex permutations. -/
def vertexPermutations : List (Equiv.Perm (Fin 4)) :=
  permsOfList ([0, 1, 2, 3] : List (Fin 4))

theorem vertexPermutations_length : vertexPermutations.length = 24 := by
  rw [vertexPermutations, length_permsOfList]
  decide

theorem mem_vertexPermutations (σ : Equiv.Perm (Fin 4)) :
    σ ∈ vertexPermutations := by
  apply mem_permsOfList_of_mem
  intro x _
  fin_cases x <;> simp

/-- A direct-list Boolean search avoids reducing the comparatively expensive
generic `Fintype` enumeration of equivalences in every word case. -/
def InsideWord.isCovered (w : InsideWord) : Bool :=
  vertexPermutations.any fun σ =>
    decide (w.relabel σ ∈ canonicalRepresentatives)

theorem canonicalRepresentatives_coverage_check :
    ∀ w : InsideWord, w.Good → w.isCovered = true := by decide

/-- Exhaustive completeness: every one of the 450 admissible labelled words
has a vertex relabeling in the displayed list. -/
theorem canonicalRepresentatives_complete :
    ∀ w : InsideWord, w.Good →
      ∃ σ : Equiv.Perm (Fin 4),
        w.relabel σ ∈ canonicalRepresentatives := by
  intro w hw
  have hcovered := canonicalRepresentatives_coverage_check w hw
  simp only [InsideWord.isCovered, List.any_eq_true] at hcovered
  obtain ⟨σ, _, hσ⟩ := hcovered
  exact ⟨σ, of_decide_eq_true hσ⟩

/-- One compact checked table verifies that every two distinct displayed
words remain distinct under every one of the 24 permutations. -/
def representativesSeparatedCheck : Bool :=
  canonicalRepresentatives.all fun u =>
    canonicalRepresentatives.all fun v =>
      decide (u = v) ||
        vertexPermutations.all fun σ => decide (u.relabel σ ≠ v)

theorem representativesSeparatedCheck_eq_true :
    representativesSeparatedCheck = true := by decide

/-- No two distinct displayed words lie in the same free-vertex orbit. -/
theorem canonicalRepresentatives_orbit_unique :
    ∀ u ∈ canonicalRepresentatives,
      ∀ v ∈ canonicalRepresentatives,
        (∃ σ : Equiv.Perm (Fin 4), u.relabel σ = v) → u = v := by
  intro u hu v hv horbit
  by_contra huv
  obtain ⟨σ, hσ⟩ := horbit
  have hcheck := representativesSeparatedCheck_eq_true
  simp only [representativesSeparatedCheck, List.all_eq_true] at hcheck
  have huvcheck := hcheck u hu v hv
  simp [huv, List.all_eq_true] at huvcheck
  exact (huvcheck σ (mem_vertexPermutations σ)) hσ

/-- There are 450 admissible labelled inside words before quotienting by
free-vertex symmetry. -/
theorem goodWords_card :
    (Finset.univ.filter InsideWord.Good).card = 450 := by decide

theorem profileC_exists_canonical_freeRelabel
    {kind : ProfileCRowExtension.Kind}
    (ext : ProfileCFourRowBoundary.FourExtension kind) :
    ∃ σ : Equiv.Perm (Fin 4),
      InsideWord.ofColoring
          (ProfileCFourRowFreeVertexSymmetry.transportFourExtension
            σ ext).inside ∈ canonicalRepresentatives := by
  have hgood : (InsideWord.ofColoring ext.inside).Good :=
    InsideWord.good_of_rootForbidden_noMono ext.inside
      ext.insideRootForbidden ext.insideNoMono
  obtain ⟨σ, hσ⟩ := canonicalRepresentatives_complete _ hgood
  refine ⟨σ, ?_⟩
  change InsideWord.ofColoring (pullbackColoring ext.inside σ) ∈
    canonicalRepresentatives
  rw [InsideWord.ofColoring_pullback]
  exact hσ

theorem profileD_exists_canonical_freeRelabel
    {kind : ProfileDTripleJoinReduction.Kind}
    (ext : ProfileDFourRowBoundary.FourExtension kind) :
    ∃ σ : Equiv.Perm (Fin 4),
      InsideWord.ofColoring
          (ProfileDFourRowFreeVertexSymmetry.transportFourExtension
            σ ext).inside ∈ canonicalRepresentatives := by
  have hgood : (InsideWord.ofColoring ext.inside).Good :=
    InsideWord.good_of_rootForbidden_noMono ext.inside
      ext.insideRootForbidden ext.insideNoMono
  obtain ⟨σ, hσ⟩ := canonicalRepresentatives_complete _ hgood
  refine ⟨σ, ?_⟩
  change InsideWord.ofColoring (pullbackColoring ext.inside σ) ∈
    canonicalRepresentatives
  rw [InsideWord.ofColoring_pullback]
  exact hσ

#print axioms R4333.RootForbiddenK4FreeVertexOrbits.canonicalRepresentatives_complete
#print axioms R4333.RootForbiddenK4FreeVertexOrbits.canonicalRepresentatives_orbit_unique
#print axioms R4333.RootForbiddenK4FreeVertexOrbits.profileC_exists_canonical_freeRelabel
#print axioms R4333.RootForbiddenK4FreeVertexOrbits.profileD_exists_canonical_freeRelabel

end RootForbiddenK4FreeVertexOrbits
end R4333
