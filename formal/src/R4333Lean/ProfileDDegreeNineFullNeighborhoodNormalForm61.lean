import R4333Lean.ProfileDHighOwnForeignC5Skeleton61
import R4333Lean.CriticalK15PartitionClassification
import R4333Lean.CriticalTemplateSelectedPositionOrbits
import R4333Lean.ColoringAddRoot

/-!
# The full degree-nine neighbourhood in profile D

Assume the five-free-support branch at a selected profile-D tail endpoint,
and assume that its own-colour degree inside the retained 46-tail is exactly
nine.  Restoring the distinguished root gives fifteen own-colour neighbours:

* the distinguished root;
* five retained free vertices;
* five vertices in one foreign critical block; and
* four vertices in the other foreign critical block.

This file constructs that `K15` semantically, deletes the selected endpoint's
own colour, and applies the checked critical `K15` catalogue.  A kernel finite
check then gives the exact surviving normal form: after colour-preserving
normalization, the restored root lies in the canonical five-element class
whose colour is the deficient four-set.  Thus this branch is not impossible
at the `K15` level, but it has only the displayed five root positions in each
of the two critical templates.

No SAT result or unverified catalogue claim is used.
-/

namespace R4333
namespace ProfileDDegreeNineFullNeighborhoodNormalForm61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open CriticalK15PartitionClassification

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FiveSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension

/-! ## Exact foreign supports in the degree-nine branch -/

/-- An explicit enumeration of an exact foreign support of size `n`. -/
structure ExactForeignSupport {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3) (n : Nat) where
  targetNeSource : target ≠ ext.block
  supportCard : (foreignOwnSupport ext target).card = n
  embedding : Fin n ↪ Fin (blockSize target)
  embeddingRange :
    Finset.univ.image embedding = foreignOwnSupport ext target

theorem exists_exactForeignSupport {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3) (n : Nat)
    (htarget : target ≠ ext.block)
    (hcard : (foreignOwnSupport ext target).card = n) :
    Nonempty (ExactForeignSupport ext target n) := by
  classical
  let support := foreignOwnSupport ext target
  have hcardLe : Fintype.card (Fin n) ≤ support.card := by
    simp [support, hcard]
  obtain ⟨embedding, hembedding⟩ :=
    Function.Embedding.exists_of_card_le_finset hcardLe
  have hmem (a : Fin n) : embedding a ∈ support :=
    hembedding ⟨a, rfl⟩
  have himage : Finset.univ.image embedding = support := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
      exact hmem a
    · rw [show support.card = n by simpa [support] using hcard]
      rw [Finset.card_image_of_injective _ embedding.injective]
      simp
  exact ⟨{
    targetNeSource := htarget
    supportCard := hcard
    embedding := embedding
    embeddingRange := by simpa [support] using himage
  }⟩

/-- In the chosen orientation, `true` means that the first foreign block is
the five-set; `false` means that the second foreign block is the five-set. -/
def largeForeignBlock (source : Fin 3) (firstLarge : Bool) : Fin 3 :=
  if firstLarge then firstForeignBlock source else secondForeignBlock source

def smallForeignBlock (source : Fin 3) (firstLarge : Bool) : Fin 3 :=
  if firstLarge then secondForeignBlock source else firstForeignBlock source

@[simp] theorem largeForeignBlock_ne_source
    (source : Fin 3) (firstLarge : Bool) :
    largeForeignBlock source firstLarge ≠ source := by
  cases firstLarge <;> simp [largeForeignBlock]

@[simp] theorem smallForeignBlock_ne_source
    (source : Fin 3) (firstLarge : Bool) :
    smallForeignBlock source firstLarge ≠ source := by
  cases firstLarge <;> simp [smallForeignBlock]

@[simp] theorem largeForeignBlock_ne_smallForeignBlock
    (source : Fin 3) (firstLarge : Bool) :
    largeForeignBlock source firstLarge ≠
      smallForeignBlock source firstLarge := by
  cases firstLarge with
  | false =>
      simpa [largeForeignBlock, smallForeignBlock] using
        (firstForeignBlock_ne_second source).symm
  | true =>
      simpa [largeForeignBlock, smallForeignBlock] using
        firstForeignBlock_ne_second source

/-- The exact `(5,4)` foreign split, with the larger block placed first in
the abstract coordinates independently of its physical block order. -/
structure DegreeNineSkeleton {kind : Kind}
    (ext : FiveSupportExtension kind) : Type where
  tailOwnDegreeNine :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) = 9
  firstLarge : Bool
  freeSupportCycle : FreeSupportC5 ext
  largeSupport : ExactForeignSupport ext
    (largeForeignBlock ext.block firstLarge) 5
  smallSupport : ExactForeignSupport ext
    (smallForeignBlock ext.block firstLarge) 4

theorem exists_degreeNineSkeleton {kind : Kind}
    (ext : FiveSupportExtension kind)
    (hdegree :
      colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor ext.block)
          (blockVertex ext.block ext.position.val) = 9) :
    Nonempty (DegreeNineSkeleton ext) := by
  have hfirstCap := foreignOwnSupport_card_le_five ext
    (firstForeignBlock ext.block) (firstForeignBlock_ne ext.block)
  have hsecondCap := foreignOwnSupport_card_le_five ext
    (secondForeignBlock ext.block) (secondForeignBlock_ne ext.block)
  have hsum := selectedTailOwnDegree_eq_foreignSum ext
  have hcases :
      ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 ∧
        (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 4) ∨
      ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 4 ∧
        (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5) := by
    omega
  rcases hcases with hfirstLarge | hsecondLarge
  · obtain ⟨large⟩ := exists_exactForeignSupport ext
      (firstForeignBlock ext.block) 5
      (firstForeignBlock_ne ext.block) hfirstLarge.1
    obtain ⟨small⟩ := exists_exactForeignSupport ext
      (secondForeignBlock ext.block) 4
      (secondForeignBlock_ne ext.block) hfirstLarge.2
    exact ⟨{
      tailOwnDegreeNine := hdegree
      firstLarge := true
      freeSupportCycle := ext.exists_inside_cycle_relabel
      largeSupport := by simpa [largeForeignBlock] using large
      smallSupport := by simpa [smallForeignBlock] using small
    }⟩
  · obtain ⟨large⟩ := exists_exactForeignSupport ext
      (secondForeignBlock ext.block) 5
      (secondForeignBlock_ne ext.block) hsecondLarge.2
    obtain ⟨small⟩ := exists_exactForeignSupport ext
      (firstForeignBlock ext.block) 4
      (firstForeignBlock_ne ext.block) hsecondLarge.1
    exact ⟨{
      tailOwnDegreeNine := hdegree
      firstLarge := false
      freeSupportCycle := ext.exists_inside_cycle_relabel
      largeSupport := by simpa [largeForeignBlock] using large
      smallSupport := by simpa [smallForeignBlock] using small
    }⟩

/-! ## Fourteen neighbours other than the restored root -/

/-- Free five-set, foreign five-set, and foreign four-set. -/
abbrev RestCoordinates := (FiveVertex ⊕ FiveVertex) ⊕ Fin 4

abbrev RetainedJoinedVertex := Sum FiveVertex TailVertex

def retainedJoinedColoring {kind : Kind}
    (ext : FiveSupportExtension kind) :
    EdgeColoring RetainedJoinedVertex (Fin 4) :=
  joinColoring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rows

theorem retainedJoinedColoring_noMono {kind : Kind}
    (ext : FiveSupportExtension kind) :
    NoMonochromaticTriangle (retainedJoinedColoring ext) := by
  exact (noMono_joinColoring_iff _ _ _).2 ⟨
    ext.toDegreeFlooredFiveExtension.toFiveExtension.insideNoMono,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.noMono,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsAdmissible,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsPairCompatible⟩

def selectedEndpoint {kind : Kind} (ext : FiveSupportExtension kind) :
    RetainedJoinedVertex :=
  .inr (blockVertex ext.block ext.position.val)

/-- Embed the fourteen non-root neighbours in their actual retained graph. -/
noncomputable def restEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    RestCoordinates ↪ RetainedJoinedVertex where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr a) => .inr (blockVertex
        (largeForeignBlock ext.block skeleton.firstLarge)
        (skeleton.largeSupport.embedding a).val)
    | .inr a => .inr (blockVertex
        (smallForeignBlock ext.block skeleton.firstLarge)
        (skeleton.smallSupport.embedding a).val)
  inj' := by
    intro x y hxy
    rcases x with (x | x)
    · rcases x with (a | a)
      · rcases y with (y | b)
        · rcases y with (b | b)
          · change (Sum.inl a : RetainedJoinedVertex) = Sum.inl b at hxy
            have hab : a = b := Sum.inl.inj hxy
            exact congrArg (fun z => Sum.inl (Sum.inl z)) hab
          · cases hxy
        · cases hxy
      · rcases y with (y | b)
        · rcases y with (b | b)
          · cases hxy
          · have hvertex := Sum.inr.inj hxy
            have hab := skeleton.largeSupport.embedding.injective
              (blockVertex_fixed_injective _ hvertex)
            exact congrArg (fun z => Sum.inl (Sum.inr z)) hab
        · have hvertex := Sum.inr.inj hxy
          exact (blockVertex_ne_of_block_ne
            (largeForeignBlock ext.block skeleton.firstLarge)
            (smallForeignBlock ext.block skeleton.firstLarge)
            (largeForeignBlock_ne_smallForeignBlock _ _)
            (skeleton.largeSupport.embedding a).isLt
            (skeleton.smallSupport.embedding b).isLt hvertex).elim
    · rcases y with (y | b)
      · rcases y with (b | b)
        · cases hxy
        · have hvertex := Sum.inr.inj hxy
          exact (blockVertex_ne_of_block_ne
            (smallForeignBlock ext.block skeleton.firstLarge)
            (largeForeignBlock ext.block skeleton.firstLarge)
            (largeForeignBlock_ne_smallForeignBlock _ _).symm
            (skeleton.smallSupport.embedding x).isLt
            (skeleton.largeSupport.embedding b).isLt hvertex).elim
      · have hvertex := Sum.inr.inj hxy
        have hab := skeleton.smallSupport.embedding.injective
          (blockVertex_fixed_injective _ hvertex)
        exact congrArg Sum.inr hab

noncomputable def restColoring {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    EdgeColoring RestCoordinates (Fin 4) :=
  pullbackColoring (retainedJoinedColoring ext) (restEmbedding skeleton)

theorem restColoring_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    NoMonochromaticTriangle (restColoring skeleton) := by
  exact noMono_pullback (retainedJoinedColoring ext)
    (restEmbedding skeleton) (restEmbedding skeleton).injective
    (retainedJoinedColoring_noMono ext)

/-- The colour from the distinguished root to each of the fourteen
neighbours. -/
def restRootColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    RestCoordinates → Fin 4
  | .inl (.inl _) => 0
  | .inl (.inr _) =>
      blockRootColor (largeForeignBlock ext.block skeleton.firstLarge)
  | .inr _ =>
      blockRootColor (smallForeignBlock ext.block skeleton.firstLarge)

theorem blockRootColor_injective : Function.Injective blockRootColor := by
  intro source target hcolor
  exact Fin.succ_injective 3 hcolor

theorem largeRootColor_ne_smallRootColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    blockRootColor (largeForeignBlock ext.block skeleton.firstLarge) ≠
      blockRootColor (smallForeignBlock ext.block skeleton.firstLarge) :=
  blockRootColor_injective.ne
    (largeForeignBlock_ne_smallForeignBlock _ _)

theorem restColoring_rootForbidden {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x y : RestCoordinates) (hxy : x ≠ y)
    (hsame : restRootColor skeleton x = restRootColor skeleton y) :
    restColoring skeleton x y ≠ restRootColor skeleton x := by
  rcases x with (x | x)
  · rcases x with (a | a)
    · rcases y with (y | b)
      · rcases y with (b | b)
        · have hab : a ≠ b := fun hab => hxy (congrArg (fun z =>
              Sum.inl (Sum.inl z)) hab)
          simpa [restColoring, restEmbedding, restRootColor,
            retainedJoinedColoring, pullbackColoring, joinColoring] using
            ext.toDegreeFlooredFiveExtension.toFiveExtension.insideRootForbidden
              a b hab
        · exact ((blockRootColor_ne_zero
              (largeForeignBlock ext.block skeleton.firstLarge))
                hsame.symm).elim
      · exact ((blockRootColor_ne_zero
            (smallForeignBlock ext.block skeleton.firstLarge))
              hsame.symm).elim
    · rcases y with (y | b)
      · rcases y with (b | b)
        · exact ((blockRootColor_ne_zero
              (largeForeignBlock ext.block skeleton.firstLarge)) hsame).elim
        · have hab : a ≠ b := fun hab => hxy (congrArg (fun z =>
              Sum.inl (Sum.inr z)) hab)
          simpa [restColoring, restEmbedding, restRootColor,
            retainedJoinedColoring, tailBlockColoring,
            pullbackColoring, joinColoring] using
            tailBlockColoring_ne_root
              ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
              (largeForeignBlock ext.block skeleton.firstLarge)
              (skeleton.largeSupport.embedding a)
              (skeleton.largeSupport.embedding b)
              (skeleton.largeSupport.embedding.injective.ne hab)
      · exact ((largeRootColor_ne_smallRootColor skeleton) hsame).elim
  · rcases y with (y | b)
    · rcases y with (b | b)
      · exact ((blockRootColor_ne_zero
            (smallForeignBlock ext.block skeleton.firstLarge)) hsame).elim
      · exact ((largeRootColor_ne_smallRootColor skeleton) hsame.symm).elim
    · have hxb : x ≠ b := fun h => hxy (congrArg Sum.inr h)
      simpa [restColoring, restEmbedding, restRootColor,
        retainedJoinedColoring, tailBlockColoring,
        pullbackColoring, joinColoring] using
        tailBlockColoring_ne_root
          ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
          (smallForeignBlock ext.block skeleton.firstLarge)
          (skeleton.smallSupport.embedding x)
          (skeleton.smallSupport.embedding b)
          (skeleton.smallSupport.embedding.injective.ne hxb)

/-! ## Restore the distinguished root and verify the own neighbourhood -/

noncomputable def rootedHostColoring {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    EdgeColoring (Option RestCoordinates) (Fin 4) :=
  addRootColoring (restColoring skeleton) (restRootColor skeleton) 0

theorem rootedHostColoring_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    NoMonochromaticTriangle (rootedHostColoring skeleton) :=
  addRootColoring_noMono _ _ _ (restColoring_noMono skeleton)
    (restColoring_rootForbidden skeleton)

theorem exactSupport_embedding_mem {kind : Kind}
    {ext : FiveSupportExtension kind} {target : Fin 3} {n : Nat}
    (support : ExactForeignSupport ext target n) (a : Fin n) :
    support.embedding a ∈ foreignOwnSupport ext target := by
  rw [← support.embeddingRange]
  exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩

theorem selectedEndpoint_ne_restEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x : RestCoordinates) :
    selectedEndpoint ext ≠ restEmbedding skeleton x := by
  rcases x with (x | x)
  · rcases x with (a | a)
    · simp [selectedEndpoint, restEmbedding]
    · intro h
      apply blockVertex_ne_of_block_ne ext.block
        (largeForeignBlock ext.block skeleton.firstLarge)
        (largeForeignBlock_ne_source _ _).symm
        ext.position.isLt (skeleton.largeSupport.embedding a).isLt
      exact Sum.inr.inj h
  · intro h
    apply blockVertex_ne_of_block_ne ext.block
      (smallForeignBlock ext.block skeleton.firstLarge)
      (smallForeignBlock_ne_source _ _).symm
      ext.position.isLt (skeleton.smallSupport.embedding x).isLt
    exact Sum.inr.inj h

theorem selectedEndpoint_color_restEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x : RestCoordinates) :
    retainedJoinedColoring ext (selectedEndpoint ext)
        (restEmbedding skeleton x) = blockRootColor ext.block := by
  rcases x with (x | x)
  · rcases x with (a | a)
    · exact ext.allFiveOwn a
    · exact (mem_foreignOwnSupport ext
          (largeForeignBlock ext.block skeleton.firstLarge)
          (skeleton.largeSupport.embedding a)).mp
        (exactSupport_embedding_mem skeleton.largeSupport a)
  · exact (mem_foreignOwnSupport ext
        (smallForeignBlock ext.block skeleton.firstLarge)
        (skeleton.smallSupport.embedding x)).mp
      (exactSupport_embedding_mem skeleton.smallSupport x)

/-! The same fifteen vertices embedded in the genuinely rooted retained
graph.  This makes explicit that the newly added vertex is the original
distinguished root, rather than an abstract auxiliary vertex. -/

def retainedRootColor : RetainedJoinedVertex → Fin 4
  | .inl _ => 0
  | .inr x => ProfileDFourRowDegreeCap.tailRootColor x

def rootedRetainedColoring {kind : Kind}
    (ext : FiveSupportExtension kind) :
    EdgeColoring (Option RetainedJoinedVertex) (Fin 4) :=
  addRootColoring (retainedJoinedColoring ext) retainedRootColor 0

theorem restRootColor_eq_retainedRootColor_restEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x : RestCoordinates) :
    restRootColor skeleton x =
      retainedRootColor (restEmbedding skeleton x) := by
  rcases x with (x | x)
  · rcases x with (a | a)
    · rfl
    · simp [restRootColor, retainedRootColor, restEmbedding,
        tailRootColor_blockVertex]
  · simp [restRootColor, retainedRootColor, restEmbedding,
      tailRootColor_blockVertex]

theorem restColoring_avoids_selectedOwnColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x y : RestCoordinates) (hxy : x ≠ y) :
    restColoring skeleton x y ≠ blockRootColor ext.block := by
  intro hedge
  apply retainedJoinedColoring_noMono ext
    (selectedEndpoint ext) (restEmbedding skeleton x)
      (restEmbedding skeleton y)
  · exact ⟨selectedEndpoint_ne_restEmbedding skeleton x,
      selectedEndpoint_ne_restEmbedding skeleton y,
      (restEmbedding skeleton).injective.ne hxy⟩
  · exact ⟨
      (selectedEndpoint_color_restEmbedding skeleton x).trans
        (selectedEndpoint_color_restEmbedding skeleton y).symm,
      (selectedEndpoint_color_restEmbedding skeleton y).trans hedge.symm⟩

theorem restRootColor_ne_selectedOwnColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x : RestCoordinates) :
    restRootColor skeleton x ≠ blockRootColor ext.block := by
  rcases x with (x | x)
  · rcases x with (a | a)
    · exact (blockRootColor_ne_zero ext.block).symm
    · exact blockRootColor_injective.ne
        (largeForeignBlock_ne_source ext.block skeleton.firstLarge)
  · exact blockRootColor_injective.ne
      (smallForeignBlock_ne_source ext.block skeleton.firstLarge)

theorem rootedHostColoring_avoids_selectedOwnColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x y : Option RestCoordinates) (hxy : x ≠ y) :
    rootedHostColoring skeleton x y ≠ blockRootColor ext.block := by
  cases x with
  | none =>
      cases y with
      | none => exact (hxy rfl).elim
      | some y => exact restRootColor_ne_selectedOwnColor skeleton y
  | some x =>
      cases y with
      | none => exact restRootColor_ne_selectedOwnColor skeleton x
      | some y =>
          exact restColoring_avoids_selectedOwnColor skeleton x y
            (fun h => hxy (congrArg some h))

/-! ## Relabel to `Fin 15`, delete the own colour, and apply the catalogue -/

noncomputable def fin15EquivRootedRest :
    Fin 15 ≃ Option RestCoordinates :=
  Fintype.equivOfCardEq (by simp [RestCoordinates, FiveVertex])

noncomputable def hostNeighborhoodColoring {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    EdgeColoring (Fin 15) (Fin 4) :=
  relabelVertices (rootedHostColoring skeleton) fin15EquivRootedRest

theorem hostNeighborhoodColoring_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    NoMonochromaticTriangle (hostNeighborhoodColoring skeleton) :=
  noMono_relabelVertices _ fin15EquivRootedRest
    (rootedHostColoring_noMono skeleton)

theorem hostNeighborhoodColoring_avoids_selectedOwnColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (u v : Fin 15) (huv : u ≠ v) :
    hostNeighborhoodColoring skeleton u v ≠ blockRootColor ext.block := by
  exact rootedHostColoring_avoids_selectedOwnColor skeleton
    (fin15EquivRootedRest u) (fin15EquivRootedRest v)
    (fin15EquivRootedRest.injective.ne huv)

noncomputable def encodedNeighborhoodColoring {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    EdgeColoring (Fin 15) ThreeColor :=
  decodeNonBlockColoring (blockRootColor ext.block)
    (hostNeighborhoodColoring skeleton)

theorem encodedNeighborhoodColoring_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    NoMonochromaticTriangle (encodedNeighborhoodColoring skeleton) := by
  exact decodeNonBlockColoring_noMono (blockRootColor ext.block)
    (hostNeighborhoodColoring skeleton)
    (hostNeighborhoodColoring_noMono skeleton)
    (hostNeighborhoodColoring_avoids_selectedOwnColor skeleton)

theorem exists_colorPreservingTemplate {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    ∃ twisted : Bool, ∃ vertex : Fin 15 ≃ Fin 15,
      ∀ u v, u ≠ v →
        encodedNeighborhoodColoring skeleton (vertex u) (vertex v) =
          k15Template twisted u v :=
  exists_colorPreserving_k15Template
    (encodedNeighborhoodColoring skeleton)
    (encodedNeighborhoodColoring_noMono skeleton)

/-! ## The restored root has the exact `(5,5,4)` colour-degree row -/

noncomputable def freeDecodedColor {kind : Kind}
    (ext : FiveSupportExtension kind) : ThreeColor :=
  decodeNonBlockColor (blockRootColor ext.block) 0

noncomputable def largeDecodedColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    ThreeColor :=
  decodeNonBlockColor (blockRootColor ext.block)
    (blockRootColor (largeForeignBlock ext.block skeleton.firstLarge))

noncomputable def smallDecodedColor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    ThreeColor :=
  decodeNonBlockColor (blockRootColor ext.block)
    (blockRootColor (smallForeignBlock ext.block skeleton.firstLarge))

theorem decodeNonBlockColor_injective_of_ne
    (block q r : Fin 4) (hq : q ≠ block) (hr : r ≠ block)
    (hdecode : decodeNonBlockColor block q =
      decodeNonBlockColor block r) : q = r := by
  have hmapped := congrArg (canonicalPalette block) hdecode
  rw [canonicalPalette_decodeNonBlockColor block q hq,
    canonicalPalette_decodeNonBlockColor block r hr] at hmapped
  exact hmapped

theorem decodedColors_pairwiseDistinct {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    PairwiseDistinct (freeDecodedColor ext)
      (largeDecodedColor skeleton) (smallDecodedColor skeleton) := by
  constructor
  · intro h
    have hhost := decodeNonBlockColor_injective_of_ne
      (blockRootColor ext.block) 0
      (blockRootColor (largeForeignBlock ext.block skeleton.firstLarge))
      (blockRootColor_ne_zero ext.block).symm
      (blockRootColor_injective.ne
        (largeForeignBlock_ne_source ext.block skeleton.firstLarge)) h
    exact (blockRootColor_ne_zero
      (largeForeignBlock ext.block skeleton.firstLarge)) hhost.symm
  · constructor
    · intro h
      have hhost := decodeNonBlockColor_injective_of_ne
        (blockRootColor ext.block) 0
        (blockRootColor (smallForeignBlock ext.block skeleton.firstLarge))
        (blockRootColor_ne_zero ext.block).symm
        (blockRootColor_injective.ne
          (smallForeignBlock_ne_source ext.block skeleton.firstLarge)) h
      exact (blockRootColor_ne_zero
        (smallForeignBlock ext.block skeleton.firstLarge)) hhost.symm
    · intro h
      have hhost := decodeNonBlockColor_injective_of_ne
        (blockRootColor ext.block)
        (blockRootColor (largeForeignBlock ext.block skeleton.firstLarge))
        (blockRootColor (smallForeignBlock ext.block skeleton.firstLarge))
        (blockRootColor_injective.ne
          (largeForeignBlock_ne_source ext.block skeleton.firstLarge))
        (blockRootColor_injective.ne
          (smallForeignBlock_ne_source ext.block skeleton.firstLarge)) h
      exact (largeRootColor_ne_smallRootColor skeleton) hhost

noncomputable def decodedRootedColoring {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    EdgeColoring (Option RestCoordinates) ThreeColor where
  color u v := decodeNonBlockColor (blockRootColor ext.block)
    (rootedHostColoring skeleton u v)
  color_symm u v := congrArg
    (decodeNonBlockColor (blockRootColor ext.block))
    ((rootedHostColoring skeleton).color_symm u v)

theorem encodedNeighborhoodColoring_eq_relabel {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    encodedNeighborhoodColoring skeleton =
      relabelVertices (decodedRootedColoring skeleton)
        fin15EquivRootedRest := by
  rfl

noncomputable def restoredRootLabel : Fin 15 :=
  fin15EquivRootedRest.symm none

noncomputable def restLabel (x : RestCoordinates) : Fin 15 :=
  fin15EquivRootedRest.symm (some x)

noncomputable def fullNeighborhoodEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    Fin 15 ↪ Option RetainedJoinedVertex where
  toFun i := (fin15EquivRootedRest i).map (restEmbedding skeleton)
  inj' := by
    intro i j hij
    apply fin15EquivRootedRest.injective
    apply (show Function.Injective
      (Option.map (restEmbedding skeleton)) by
        intro x y hxy
        rcases x with (_ | x) <;> rcases y with (_ | y)
        · rfl
        · cases hxy
        · cases hxy
        · exact congrArg some
            ((restEmbedding skeleton).injective (Option.some.inj hxy)))
    exact hij

@[simp] theorem fullNeighborhoodEmbedding_root {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    fullNeighborhoodEmbedding skeleton restoredRootLabel = none := by
  simp [fullNeighborhoodEmbedding, restoredRootLabel]

@[simp] theorem fullNeighborhoodEmbedding_rest {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x : RestCoordinates) :
    fullNeighborhoodEmbedding skeleton (restLabel x) =
      some (restEmbedding skeleton x) := by
  simp [fullNeighborhoodEmbedding, restLabel]

/-- Every displayed vertex is an own-colour neighbour of the selected
endpoint after the actual distinguished root is restored. -/
theorem fullNeighborhoodEmbedding_is_selectedOwnNeighbor {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (i : Fin 15) :
    rootedRetainedColoring ext (some (selectedEndpoint ext))
        (fullNeighborhoodEmbedding skeleton i) = blockRootColor ext.block := by
  change rootedRetainedColoring ext (some (selectedEndpoint ext))
      ((fin15EquivRootedRest i).map (restEmbedding skeleton)) = _
  cases hcoordinate : fin15EquivRootedRest i with
  | none =>
      change ProfileDFourRowDegreeCap.tailRootColor
        (blockVertex ext.block ext.position.val) = blockRootColor ext.block
      exact tailRootColor_blockVertex ext.block ext.position
  | some x =>
      change retainedJoinedColoring ext (selectedEndpoint ext)
        (restEmbedding skeleton x) = blockRootColor ext.block
      exact selectedEndpoint_color_restEmbedding skeleton x

theorem colorDegree_relabel_equiv
    {V W C : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [DecidableEq C]
    (c : EdgeColoring V C) (e : W ≃ V) (q : C) (w : W) :
    colorDegree (relabelVertices c e) q w = colorDegree c q (e w) := by
  change (colorNeighborhood (relabelVertices c e) q w).card =
    (colorNeighborhood c q (e w)).card
  exact Finset.card_equiv e fun x => by
    simp only [mem_colorNeighborhood, relabelVertices_apply]
    constructor
    · rintro ⟨hxw, hcolor⟩
      exact ⟨e.injective.ne hxw, hcolor⟩
    · rintro ⟨hexw, hcolor⟩
      exact ⟨fun hxw => hexw (congrArg e hxw), hcolor⟩

theorem decodedRootedColoring_degree_free {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    colorDegree (decodedRootedColoring skeleton) (freeDecodedColor ext) none = 5 := by
  classical
  have hcolors := decodedColors_pairwiseDistinct skeleton
  have hlargeFree :
      decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (largeForeignBlock ext.block skeleton.firstLarge)) ≠
        decodeNonBlockColor (blockRootColor ext.block) 0 := by
    simpa [largeDecodedColor, freeDecodedColor] using hcolors.1.symm
  have hsmallFree :
      decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (smallForeignBlock ext.block skeleton.firstLarge)) ≠
        decodeNonBlockColor (blockRootColor ext.block) 0 := by
    simpa [smallDecodedColor, freeDecodedColor] using hcolors.2.1.symm
  let embedding : FiveVertex ↪ Option RestCoordinates := {
    toFun := fun a => some (.inl (.inl a))
    inj' := by intro a b h; exact Sum.inl.inj (Sum.inl.inj (Option.some.inj h))
  }
  have hset : colorNeighborhood (decodedRootedColoring skeleton)
      (freeDecodedColor ext) none = Finset.univ.image embedding := by
    ext w
    rcases w with (_ | w)
    · simp [colorNeighborhood]
    · rcases w with (w | w)
      · rcases w with (a | a) <;>
          simp [colorNeighborhood, decodedRootedColoring,
            rootedHostColoring, restRootColor, freeDecodedColor,
            largeDecodedColor, smallDecodedColor, embedding,
            hlargeFree]
      · simp [colorNeighborhood, decodedRootedColoring,
          rootedHostColoring, restRootColor, freeDecodedColor,
          largeDecodedColor, smallDecodedColor, embedding,
          hsmallFree]
  rw [colorDegree, hset,
    Finset.card_image_of_injective _ embedding.injective]
  simp [FiveVertex]

theorem decodedRootedColoring_degree_large {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    colorDegree (decodedRootedColoring skeleton)
      (largeDecodedColor skeleton) none = 5 := by
  classical
  have hcolors := decodedColors_pairwiseDistinct skeleton
  have hfreeLarge :
      decodeNonBlockColor (blockRootColor ext.block) 0 ≠
        decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (largeForeignBlock ext.block skeleton.firstLarge)) := by
    simpa [freeDecodedColor, largeDecodedColor] using hcolors.1
  have hsmallLarge :
      decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (smallForeignBlock ext.block skeleton.firstLarge)) ≠
        decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (largeForeignBlock ext.block skeleton.firstLarge)) := by
    simpa [smallDecodedColor, largeDecodedColor] using hcolors.2.2.symm
  let embedding : FiveVertex ↪ Option RestCoordinates := {
    toFun := fun a => some (.inl (.inr a))
    inj' := by intro a b h; exact Sum.inr.inj (Sum.inl.inj (Option.some.inj h))
  }
  have hset : colorNeighborhood (decodedRootedColoring skeleton)
      (largeDecodedColor skeleton) none = Finset.univ.image embedding := by
    ext w
    rcases w with (_ | w)
    · simp [colorNeighborhood]
    · rcases w with (w | w)
      · rcases w with (a | a) <;>
          simp [colorNeighborhood, decodedRootedColoring,
            rootedHostColoring, restRootColor, freeDecodedColor,
            largeDecodedColor, smallDecodedColor, embedding,
            hfreeLarge]
      · simp [colorNeighborhood, decodedRootedColoring,
          rootedHostColoring, restRootColor, freeDecodedColor,
          largeDecodedColor, smallDecodedColor, embedding,
          hsmallLarge]
  rw [colorDegree, hset,
    Finset.card_image_of_injective _ embedding.injective]
  simp [FiveVertex]

theorem decodedRootedColoring_degree_small {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    colorDegree (decodedRootedColoring skeleton)
      (smallDecodedColor skeleton) none = 4 := by
  classical
  have hcolors := decodedColors_pairwiseDistinct skeleton
  have hfreeSmall :
      decodeNonBlockColor (blockRootColor ext.block) 0 ≠
        decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (smallForeignBlock ext.block skeleton.firstLarge)) := by
    simpa [freeDecodedColor, smallDecodedColor] using hcolors.2.1
  have hlargeSmall :
      decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (largeForeignBlock ext.block skeleton.firstLarge)) ≠
        decodeNonBlockColor (blockRootColor ext.block)
          (blockRootColor
            (smallForeignBlock ext.block skeleton.firstLarge)) := by
    simpa [largeDecodedColor, smallDecodedColor] using hcolors.2.2
  let embedding : Fin 4 ↪ Option RestCoordinates := {
    toFun := fun a => some (.inr a)
    inj' := by intro a b h; exact Sum.inr.inj (Option.some.inj h)
  }
  have hset : colorNeighborhood (decodedRootedColoring skeleton)
      (smallDecodedColor skeleton) none = Finset.univ.image embedding := by
    ext w
    rcases w with (_ | w)
    · simp [colorNeighborhood]
    · rcases w with (w | w)
      · rcases w with (a | a) <;>
          simp [colorNeighborhood, decodedRootedColoring,
            rootedHostColoring, restRootColor, freeDecodedColor,
            largeDecodedColor, smallDecodedColor, embedding,
            hfreeSmall, hlargeSmall]
      · simp [colorNeighborhood, decodedRootedColoring,
          rootedHostColoring, restRootColor, freeDecodedColor,
          largeDecodedColor, smallDecodedColor, embedding]
  rw [colorDegree, hset,
    Finset.card_image_of_injective _ embedding.injective]
  simp

theorem encodedNeighborhoodColoring_degree_free {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    colorDegree (encodedNeighborhoodColoring skeleton)
      (freeDecodedColor ext) restoredRootLabel = 5 := by
  rw [encodedNeighborhoodColoring_eq_relabel,
    colorDegree_relabel_equiv]
  simpa [restoredRootLabel] using
    decodedRootedColoring_degree_free skeleton

theorem encodedNeighborhoodColoring_degree_large {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    colorDegree (encodedNeighborhoodColoring skeleton)
      (largeDecodedColor skeleton) restoredRootLabel = 5 := by
  rw [encodedNeighborhoodColoring_eq_relabel,
    colorDegree_relabel_equiv]
  simpa [restoredRootLabel] using
    decodedRootedColoring_degree_large skeleton

theorem encodedNeighborhoodColoring_degree_small {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    colorDegree (encodedNeighborhoodColoring skeleton)
      (smallDecodedColor skeleton) restoredRootLabel = 4 := by
  rw [encodedNeighborhoodColoring_eq_relabel,
    colorDegree_relabel_equiv]
  simpa [restoredRootLabel] using
    decodedRootedColoring_degree_small skeleton

/-! ## Exhaustive finite classification inside the two templates -/

/-- For either critical template and any ordering of the three colours, a
vertex has ordered degree row `(5,5,4)` exactly when it belongs to the
canonical part indexed by the deficient third colour. -/
theorem template_degree_five_five_four_iff_canonicalPart :
    ∀ (twisted : Bool) (first second deficient : ThreeColor)
      (root : Fin 15),
      PairwiseDistinct first second deficient →
      (colorDegree (k15Template twisted) first root = 5 ∧
        colorDegree (k15Template twisted) second root = 5 ∧
        colorDegree (k15Template twisted) deficient root = 4 ↔
        root ∈ canonicalPart twisted deficient) := by
  intro twisted first second deficient root hdistinct
  cases twisted <;> fin_cases first <;> fin_cases second <;>
    fin_cases deficient <;> simp_all [PairwiseDistinct] <;>
    fin_cases root <;> decide

/-- Off-diagonal colour equality through a vertex normalization preserves
the colour degree at the corresponding vertex. -/
theorem colorDegree_eq_of_normalizes
    (source target : EdgeColoring (Fin 15) ThreeColor)
    (vertex : Fin 15 ≃ Fin 15)
    (hnormalizes : ∀ u v, u ≠ v →
      source (vertex u) (vertex v) = target u v)
    (q : ThreeColor) (u : Fin 15) :
    colorDegree target q u = colorDegree source q (vertex u) := by
  change (colorNeighborhood target q u).card =
    (colorNeighborhood source q (vertex u)).card
  exact Finset.card_equiv vertex fun v => by
    simp only [mem_colorNeighborhood]
    constructor
    · rintro ⟨hvu, hcolor⟩
      exact ⟨vertex.injective.ne hvu,
        (hnormalizes u v hvu.symm).trans hcolor⟩
    · rintro ⟨hvertex, hcolor⟩
      have hvu : v ≠ u := fun h => hvertex (congrArg vertex h)
      exact ⟨hvu, (hnormalizes u v hvu.symm).symm.trans hcolor⟩

/-- Strongest finite normal form obtained from the full degree-nine
neighbourhood.  The three concrete groups remain groupwise constant from
the root, and the template root is one of the exact five labels in the
canonical deficient part. -/
structure DegreeNineFullNeighborhoodNormalForm {kind : Kind}
    (ext : FiveSupportExtension kind) (skeleton : DegreeNineSkeleton ext) where
  twisted : Bool
  vertex : Fin 15 ≃ Fin 15
  normalizes : ∀ u v, u ≠ v →
    encodedNeighborhoodColoring skeleton (vertex u) (vertex v) =
      k15Template twisted u v
  freeDegree : colorDegree (k15Template twisted) (freeDecodedColor ext)
    (vertex.symm restoredRootLabel) = 5
  largeDegree : colorDegree (k15Template twisted)
    (largeDecodedColor skeleton) (vertex.symm restoredRootLabel) = 5
  smallDegree : colorDegree (k15Template twisted)
    (smallDecodedColor skeleton) (vertex.symm restoredRootLabel) = 4
  rootInCanonicalDeficientPart :
    vertex.symm restoredRootLabel ∈
      canonicalPart twisted (smallDecodedColor skeleton)
  rootToFreeConstant : ∀ a : FiveVertex,
    k15Template twisted (vertex.symm restoredRootLabel)
        (vertex.symm (restLabel (.inl (.inl a)))) = freeDecodedColor ext
  rootToLargeConstant : ∀ a : FiveVertex,
    k15Template twisted (vertex.symm restoredRootLabel)
        (vertex.symm (restLabel (.inl (.inr a)))) =
      largeDecodedColor skeleton
  rootToSmallConstant : ∀ a : Fin 4,
    k15Template twisted (vertex.symm restoredRootLabel)
        (vertex.symm (restLabel (.inr a))) = smallDecodedColor skeleton

theorem restoredRootLabel_ne_restLabel (x : RestCoordinates) :
    restoredRootLabel ≠ restLabel x := by
  intro h
  have h' := congrArg fin15EquivRootedRest h
  simpa [restoredRootLabel, restLabel] using h'

theorem encodedNeighborhoodColoring_root_rest {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext)
    (x : RestCoordinates) :
    encodedNeighborhoodColoring skeleton restoredRootLabel (restLabel x) =
      decodeNonBlockColor (blockRootColor ext.block)
        (restRootColor skeleton x) := by
  change decodeNonBlockColor (blockRootColor ext.block)
      (rootedHostColoring skeleton
        (fin15EquivRootedRest restoredRootLabel)
        (fin15EquivRootedRest (restLabel x))) = _
  rw [show fin15EquivRootedRest restoredRootLabel = none by
        simp [restoredRootLabel],
    show fin15EquivRootedRest (restLabel x) = some x by
        simp [restLabel]]
  rfl

theorem exists_degreeNineFullNeighborhoodNormalForm {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    Nonempty (DegreeNineFullNeighborhoodNormalForm ext skeleton) := by
  obtain ⟨twisted, vertex, hnormalizes⟩ :=
    exists_colorPreservingTemplate skeleton
  have hrootMap : vertex (vertex.symm restoredRootLabel) =
      restoredRootLabel := vertex.apply_symm_apply restoredRootLabel
  have hfreeDegree :
      colorDegree (k15Template twisted) (freeDecodedColor ext)
        (vertex.symm restoredRootLabel) = 5 := by
    rw [colorDegree_eq_of_normalizes _ _ vertex hnormalizes]
    simpa [hrootMap] using encodedNeighborhoodColoring_degree_free skeleton
  have hlargeDegree :
      colorDegree (k15Template twisted) (largeDecodedColor skeleton)
        (vertex.symm restoredRootLabel) = 5 := by
    rw [colorDegree_eq_of_normalizes _ _ vertex hnormalizes]
    simpa [hrootMap] using encodedNeighborhoodColoring_degree_large skeleton
  have hsmallDegree :
      colorDegree (k15Template twisted) (smallDecodedColor skeleton)
        (vertex.symm restoredRootLabel) = 4 := by
    rw [colorDegree_eq_of_normalizes _ _ vertex hnormalizes]
    simpa [hrootMap] using encodedNeighborhoodColoring_degree_small skeleton
  refine ⟨{
    twisted := twisted
    vertex := vertex
    normalizes := hnormalizes
    freeDegree := hfreeDegree
    largeDegree := hlargeDegree
    smallDegree := hsmallDegree
    rootInCanonicalDeficientPart := ?_
    rootToFreeConstant := ?_
    rootToLargeConstant := ?_
    rootToSmallConstant := ?_
  }⟩
  · exact (template_degree_five_five_four_iff_canonicalPart
      twisted (freeDecodedColor ext) (largeDecodedColor skeleton)
      (smallDecodedColor skeleton) (vertex.symm restoredRootLabel)
      (decodedColors_pairwiseDistinct skeleton)).mp
        ⟨hfreeDegree, hlargeDegree, hsmallDegree⟩
  · intro a
    have hne : vertex.symm restoredRootLabel ≠
        vertex.symm (restLabel (.inl (.inl a))) :=
      vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inl (.inl a)))
    calc
      k15Template twisted (vertex.symm restoredRootLabel)
          (vertex.symm (restLabel (.inl (.inl a)))) =
        encodedNeighborhoodColoring skeleton restoredRootLabel
          (restLabel (.inl (.inl a))) :=
        (hnormalizes _ _ hne).symm.trans (by simp [restoredRootLabel, restLabel])
      _ = freeDecodedColor ext := by
        simpa [restRootColor, freeDecodedColor] using
          encodedNeighborhoodColoring_root_rest skeleton (.inl (.inl a))
  · intro a
    have hne : vertex.symm restoredRootLabel ≠
        vertex.symm (restLabel (.inl (.inr a))) :=
      vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inl (.inr a)))
    calc
      k15Template twisted (vertex.symm restoredRootLabel)
          (vertex.symm (restLabel (.inl (.inr a)))) =
        encodedNeighborhoodColoring skeleton restoredRootLabel
          (restLabel (.inl (.inr a))) :=
        (hnormalizes _ _ hne).symm.trans (by simp [restoredRootLabel, restLabel])
      _ = largeDecodedColor skeleton := by
        simpa [restRootColor, largeDecodedColor] using
          encodedNeighborhoodColoring_root_rest skeleton (.inl (.inr a))
  · intro a
    have hne : vertex.symm restoredRootLabel ≠
        vertex.symm (restLabel (.inr a)) :=
      vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inr a))
    calc
      k15Template twisted (vertex.symm restoredRootLabel)
          (vertex.symm (restLabel (.inr a))) =
        encodedNeighborhoodColoring skeleton restoredRootLabel
          (restLabel (.inr a)) :=
        (hnormalizes _ _ hne).symm.trans (by simp [restoredRootLabel, restLabel])
      _ = smallDecodedColor skeleton := by
        simpa [restRootColor, smallDecodedColor] using
          encodedNeighborhoodColoring_root_rest skeleton (.inr a)

/-! ## Quotient by colour-preserving template automorphisms -/

/-- Once the deficient colour is fixed, the untwisted template has one
remaining root orbit and the twisted template has three. -/
def degreeNineRootRepresentativeSet
    (twisted : Bool) (deficient : ThreeColor) : Finset (Fin 15) :=
  if twisted then
    ![({0, 5, 7} : Finset (Fin 15)), {1, 4, 12}, {2, 6, 9}] deficient
  else
    ![({0} : Finset (Fin 15)), {2}, {1}] deficient

theorem degreeNineRootRepresentativeSet_card
    (twisted : Bool) (deficient : ThreeColor) :
    (degreeNineRootRepresentativeSet twisted deficient).card =
      if twisted then 3 else 1 := by
  cases twisted <;> fin_cases deficient <;> decide

/-- The existing explicit selected-position automorphism sends every label
in the deficient canonical part into the exact reduced set above. -/
theorem positionRepresentative_mem_degreeNineRootRepresentativeSet :
    ∀ (twisted : Bool) (deficient : ThreeColor) (selected : Fin 15),
      selected ∈ canonicalPart twisted deficient →
      k15PositionRepresentative twisted selected ∈
        degreeNineRootRepresentativeSet twisted deficient := by
  intro twisted deficient selected hselected
  cases twisted <;> fin_cases deficient <;> fin_cases selected <;>
    simp_all [canonicalPart, untwistedPartZero, untwistedPartOne,
      untwistedPartTwo, twistedPartZero, twistedPartOne, twistedPartTwo] <;>
    decide

/-- Orbit-reduced form.  Its vertex equivalence still normalizes the actual
semantic neighbourhood, while the restored root now occupies only one of
`1` untwisted or `3` twisted positions for its fixed deficient colour. -/
structure OrbitReducedDegreeNineFullNeighborhoodNormalForm {kind : Kind}
    (ext : FiveSupportExtension kind) (skeleton : DegreeNineSkeleton ext) where
  twisted : Bool
  vertex : Fin 15 ≃ Fin 15
  normalizes : ∀ u v, u ≠ v →
    encodedNeighborhoodColoring skeleton (vertex u) (vertex v) =
      k15Template twisted u v
  rootRepresentative :
    vertex.symm restoredRootLabel ∈
      degreeNineRootRepresentativeSet twisted (smallDecodedColor skeleton)

theorem exists_orbitReducedDegreeNineFullNeighborhoodNormalForm {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeNineSkeleton ext) :
    Nonempty (OrbitReducedDegreeNineFullNeighborhoodNormalForm ext skeleton) := by
  obtain ⟨normal⟩ := exists_degreeNineFullNeighborhoodNormalForm skeleton
  let selected : Fin 15 := normal.vertex.symm restoredRootLabel
  let automorphism : Fin 15 ≃ Fin 15 :=
    k15SelectedPositionEquiv normal.twisted selected
  let vertex : Fin 15 ≃ Fin 15 := automorphism.symm.trans normal.vertex
  have hnormalizes : ∀ u v, u ≠ v →
      encodedNeighborhoodColoring skeleton (vertex u) (vertex v) =
        k15Template normal.twisted u v := by
    intro u v huv
    calc
      encodedNeighborhoodColoring skeleton (vertex u) (vertex v) =
          k15Template normal.twisted (automorphism.symm u)
            (automorphism.symm v) := by
        exact normal.normalizes _ _ (automorphism.symm.injective.ne huv)
      _ = k15Template normal.twisted u v := by
        simpa [automorphism] using
          k15SelectedPositionEquiv_preserves normal.twisted selected
            (automorphism.symm u) (automorphism.symm v)
            (automorphism.symm.injective.ne huv)
  refine ⟨{
    twisted := normal.twisted
    vertex := vertex
    normalizes := hnormalizes
    rootRepresentative := ?_
  }⟩
  have hroot : vertex.symm restoredRootLabel =
      k15PositionRepresentative normal.twisted selected := by
    change automorphism (normal.vertex.symm restoredRootLabel) = _
    simpa [selected, automorphism] using
      k15SelectedPositionEquiv_selected normal.twisted selected
  rw [hroot]
  exact positionRepresentative_mem_degreeNineRootRepresentativeSet
    normal.twisted (smallDecodedColor skeleton) selected
    normal.rootInCanonicalDeficientPart

#print axioms exists_degreeNineSkeleton
#print axioms rootedHostColoring_noMono
#print axioms encodedNeighborhoodColoring_noMono
#print axioms template_degree_five_five_four_iff_canonicalPart
#print axioms exists_degreeNineFullNeighborhoodNormalForm
#print axioms exists_orbitReducedDegreeNineFullNeighborhoodNormalForm

end ProfileDDegreeNineFullNeighborhoodNormalForm61
end R4333
