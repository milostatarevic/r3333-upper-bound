import R4333Lean.ProfileDHighOwnFiveRowSplit61

/-!
# Foreign-block C5 skeleton at a high profile-D endpoint

In the five-free-support branch, the selected endpoint has nine or ten
own-colour neighbours in the 46-tail.  This file partitions those neighbours
between the two foreign critical blocks.  Each part has order at most five,
so their only possible sizes are `(5,5)`, `(4,5)`, and `(5,4)`.

Every saturated foreign part is internally two-coloured: its edges avoid
both the selected endpoint's own colour and the target block's root colour.
The checked two-colour `K5` classification therefore makes it a `C5` and
its complement, just like the retained free five-set.  No finite-search
refutation is asserted.
-/

namespace R4333
namespace ProfileDHighOwnForeignC5Skeleton61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FiveSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension

/-! ## The two foreign blocks and their local supports -/

/-- The two blocks other than `source`, in increasing deterministic order. -/
def firstForeignBlock : Fin 3 → Fin 3 := ![1, 0, 0]
def secondForeignBlock : Fin 3 → Fin 3 := ![2, 2, 1]

@[simp] theorem firstForeignBlock_ne (source : Fin 3) :
    firstForeignBlock source ≠ source := by
  fin_cases source <;> decide

@[simp] theorem secondForeignBlock_ne (source : Fin 3) :
    secondForeignBlock source ≠ source := by
  fin_cases source <;> decide

@[simp] theorem firstForeignBlock_ne_second (source : Fin 3) :
    firstForeignBlock source ≠ secondForeignBlock source := by
  fin_cases source <;> decide

/-- The selected endpoint's own-colour neighbours in one local tail block. -/
def foreignOwnSupport {kind : Kind} (ext : FiveSupportExtension kind)
    (target : Fin 3) : Finset (Fin (blockSize target)) :=
  Finset.univ.filter fun position =>
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex ext.block ext.position.val)
        (blockVertex target position.val) = blockRootColor ext.block

@[simp] theorem mem_foreignOwnSupport {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (position : Fin (blockSize target)) :
    position ∈ foreignOwnSupport ext target ↔
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex ext.block ext.position.val)
          (blockVertex target position.val) = blockRootColor ext.block := by
  simp [foreignOwnSupport]

/-- The target critical block, pulled back to its local coordinate type. -/
def tailBlockColoring {kind : Kind} (tail : Witness kind)
    (target : Fin 3) : EdgeColoring (Fin (blockSize target)) (Fin 4) :=
  pullbackColoring tail.coloring
    (fun position => blockVertex target position.val)

theorem tailBlockColoring_noMono {kind : Kind} (tail : Witness kind)
    (target : Fin 3) :
    NoMonochromaticTriangle (tailBlockColoring tail target) := by
  exact noMono_pullback tail.coloring _
    (blockVertex_fixed_injective target) tail.noMono

/-- Internal edges of a critical block never use that block's root colour. -/
theorem tailBlockColoring_ne_root {kind : Kind} (tail : Witness kind)
    (target : Fin 3) (left right : Fin (blockSize target))
    (hlr : left ≠ right) :
    tailBlockColoring tail target left right ≠ blockRootColor target := by
  fin_cases target
  · have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 0 (by rfl) left right hlr
    change tail.coloring (blockVertex 0 left.val)
        (blockVertex 0 right.val) ≠ (1 : Fin 4)
    rw [hedge]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 1 _
  · have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 1 (by rfl) left right hlr
    change tail.coloring (blockVertex 1 left.val)
        (blockVertex 1 right.val) ≠ (2 : Fin 4)
    rw [hedge]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 2 _
  · have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        tail 2 (by rfl) left right hlr
    change tail.coloring (blockVertex 2 left.val)
        (blockVertex 2 right.val) ≠ (3 : Fin 4)
    rw [hedge]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 3 _

/-- Two neighbours of the selected endpoint cannot have an edge in the
selected endpoint's own colour. -/
theorem foreignOwnSupport_edge_ne_own {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block)
    (left : Fin (blockSize target)) (hleft : left ∈ foreignOwnSupport ext target)
    (right : Fin (blockSize target)) (hright : right ∈ foreignOwnSupport ext target)
    (hlr : left ≠ right) :
    tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
        left right ≠ blockRootColor ext.block := by
  let tail := ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hsourceLeft :
      blockVertex ext.block ext.position.val ≠
        blockVertex target left.val :=
    blockVertex_ne_of_block_ne ext.block target htarget.symm
      ext.position.isLt left.isLt
  have hsourceRight :
      blockVertex ext.block ext.position.val ≠
        blockVertex target right.val :=
    blockVertex_ne_of_block_ne ext.block target htarget.symm
      ext.position.isLt right.isLt
  have hleftRight :
      blockVertex target left.val ≠ blockVertex target right.val :=
    (blockVertex_fixed_injective target).ne hlr
  have hleftColor := (mem_foreignOwnSupport ext target left).mp hleft
  have hrightColor := (mem_foreignOwnSupport ext target right).mp hright
  intro hedge
  apply tail.noMono
    (blockVertex ext.block ext.position.val)
    (blockVertex target left.val) (blockVertex target right.val)
  · exact ⟨hsourceLeft, hsourceRight, hleftRight⟩
  · exact ⟨hleftColor.trans hrightColor.symm,
      hrightColor.trans hedge.symm⟩

/-- The third nonzero root colour, distinct from both source and target.
The diagonal entries are irrelevant. -/
def thirdBlockRootColor (source target : Fin 3) : Fin 4 :=
  ![![0, 3, 2], ![3, 0, 1], ![2, 1, 0]] source target

theorem foreignOwnSupport_edge_color_cases {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block)
    (left : Fin (blockSize target)) (hleft : left ∈ foreignOwnSupport ext target)
    (right : Fin (blockSize target)) (hright : right ∈ foreignOwnSupport ext target)
    (hlr : left ≠ right) :
    tailBlockColoring
          ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
          left right = 0 ∨
      tailBlockColoring
          ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
          left right = thirdBlockRootColor ext.block target := by
  have hnotOwn := foreignOwnSupport_edge_ne_own
    ext target htarget left hleft right hright hlr
  have hnotTarget := tailBlockColoring_ne_root
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
      left right hlr
  generalize hcolor : tailBlockColoring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
      left right = color
  generalize hsource : ext.block = source at htarget hnotOwn hcolor ⊢
  fin_cases source <;> fin_cases target <;> fin_cases color <;>
    simp_all [blockRootColor, thirdBlockRootColor]

theorem foreignOwnSupport_card_le_five {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block) :
    (foreignOwnSupport ext target).card ≤ 5 := by
  apply twoColorFinset_card_le_five
    (tailBlockColoring
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target)
    (tailBlockColoring_noMono
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target)
    (p := (0 : Fin 4))
    (q := thirdBlockRootColor ext.block target)
    (foreignOwnSupport ext target)
  intro left hleft right hright hlr
  exact foreignOwnSupport_edge_color_cases
    ext target htarget left hleft right hright hlr

/-! ## Exact partition of the selected tail degree -/

def selectedEndpointOwnRow {kind : Kind}
    (ext : FiveSupportExtension kind) : TailVertex → Fin 4 :=
  fun y =>
    if y = blockVertex ext.block ext.position.val then 0
    else ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex ext.block ext.position.val) y

theorem selectedEndpointOwnRow_support_eq_neighborhood {kind : Kind}
    (ext : FiveSupportExtension kind) :
    rowColorSupport (selectedEndpointOwnRow ext) (blockRootColor ext.block) =
      colorNeighborhood
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) := by
  ext y
  simp only [mem_rowColorSupport, mem_colorNeighborhood]
  constructor
  · intro hy
    have hyne : y ≠ blockVertex ext.block ext.position.val := by
      intro heq
      subst y
      have hzero : (0 : Fin 4) = blockRootColor ext.block := by
        simpa [selectedEndpointOwnRow] using hy
      exact (blockRootColor_ne_zero ext.block) hzero.symm
    exact ⟨hyne, by simpa [selectedEndpointOwnRow, hyne] using hy⟩
  · rintro ⟨hyne, hycolor⟩
    simpa [selectedEndpointOwnRow, hyne] using hycolor

def endpointBlockSupport {kind : Kind} (ext : FiveSupportExtension kind)
    (target : Fin 3) : Finset (Fin (blockSize target)) :=
  rowColorSupport
    (fun position => selectedEndpointOwnRow ext
      (blockVertex target position.val))
    (blockRootColor ext.block)

theorem endpointBlockSupport_eq_foreignOwnSupport {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block) :
    endpointBlockSupport ext target = foreignOwnSupport ext target := by
  ext position
  have hvertices :
      blockVertex target position.val ≠
        blockVertex ext.block ext.position.val := by
    exact (blockVertex_ne_of_block_ne ext.block target htarget.symm
      ext.position.isLt position.isLt).symm
  simp [endpointBlockSupport, foreignOwnSupport,
    selectedEndpointOwnRow, hvertices]

theorem endpointBlockSupport_own_card_eq_zero {kind : Kind}
    (ext : FiveSupportExtension kind) :
    (endpointBlockSupport ext ext.block).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro position hposition
  have hcolor := (mem_rowColorSupport _ _ position).mp hposition
  by_cases hsame : position = ext.position
  · subst position
    have hzero : (0 : Fin 4) = blockRootColor ext.block := by
      simpa [endpointBlockSupport, selectedEndpointOwnRow] using hcolor
    exact (blockRootColor_ne_zero ext.block) hzero.symm
  · have hne :
        blockVertex ext.block position.val ≠
          blockVertex ext.block ext.position.val :=
      (blockVertex_fixed_injective ext.block).ne hsame
    have hforbidden := tailBlockColoring_ne_root
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail ext.block
      position ext.position hsame
    apply hforbidden
    change ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex ext.block position.val)
      (blockVertex ext.block ext.position.val) = blockRootColor ext.block
    rw [ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring.color_symm]
    simpa [endpointBlockSupport, selectedEndpointOwnRow, hne] using hcolor

theorem selectedTailOwnDegree_eq_threeBlockSum {kind : Kind}
    (ext : FiveSupportExtension kind) :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (endpointBlockSupport ext 0).card +
        ((endpointBlockSupport ext 1).card +
          (endpointBlockSupport ext 2).card) := by
  rw [show colorDegree
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (rowColorSupport (selectedEndpointOwnRow ext)
        (blockRootColor ext.block)).card by
      rw [selectedEndpointOwnRow_support_eq_neighborhood]
      rfl]
  have hsum := support_card_eq_block_sum
    (selectedEndpointOwnRow ext) (blockRootColor ext.block)
  have hzero :
      ProfileDBlockZeroSupport.k15Row (selectedEndpointOwnRow ext) 0 =
        fun position : Fin 15 => selectedEndpointOwnRow ext
          (blockVertex 0 position.val) := by
    rfl
  have hone :
      ProfileDBlockZeroSupport.k15Row (selectedEndpointOwnRow ext) 1 =
        fun position : Fin 15 => selectedEndpointOwnRow ext
          (blockVertex 1 position.val) := by
    rfl
  have htwo :
      ProfileDBlockZeroSupport.k16Row (selectedEndpointOwnRow ext) =
        fun position : Fin 16 => selectedEndpointOwnRow ext
          (blockVertex 2 position.val) := by
    rfl
  rw [hzero, hone, htwo] at hsum
  simpa [endpointBlockSupport,
    ProfileDTripleJoinReduction.blockSize] using hsum

theorem threeBlockSum_eq_source_foreignSum
    (f : Fin 3 → Nat) (source : Fin 3) :
    f 0 + (f 1 + f 2) =
      f source +
        (f (firstForeignBlock source) + f (secondForeignBlock source)) := by
  fin_cases source <;> simp [firstForeignBlock, secondForeignBlock] <;> omega

theorem selectedTailOwnDegree_eq_foreignSum {kind : Kind}
    (ext : FiveSupportExtension kind) :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (foreignOwnSupport ext (firstForeignBlock ext.block)).card +
        (foreignOwnSupport ext (secondForeignBlock ext.block)).card := by
  have hall := selectedTailOwnDegree_eq_threeBlockSum ext
  have hown := endpointBlockSupport_own_card_eq_zero ext
  have hfirst := endpointBlockSupport_eq_foreignOwnSupport ext
    (firstForeignBlock ext.block) (firstForeignBlock_ne ext.block)
  have hsecond := endpointBlockSupport_eq_foreignOwnSupport ext
    (secondForeignBlock ext.block) (secondForeignBlock_ne ext.block)
  calc
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (endpointBlockSupport ext 0).card +
        ((endpointBlockSupport ext 1).card +
          (endpointBlockSupport ext 2).card) := hall
    _ = (endpointBlockSupport ext ext.block).card +
        ((endpointBlockSupport ext (firstForeignBlock ext.block)).card +
          (endpointBlockSupport ext
            (secondForeignBlock ext.block)).card) :=
      threeBlockSum_eq_source_foreignSum
        (fun target => (endpointBlockSupport ext target).card) ext.block
    _ = (foreignOwnSupport ext (firstForeignBlock ext.block)).card +
        (foreignOwnSupport ext (secondForeignBlock ext.block)).card := by
      rw [hown, hfirst, hsecond]
      omega

/-- The exhaustive pair of foreign support sizes. -/
theorem foreignSupport_size_cases {kind : Kind}
    (ext : FiveSupportExtension kind) :
    ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 ∧
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5) ∨
    ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 4 ∧
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5) ∨
    ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 ∧
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 4) := by
  have hfirst := foreignOwnSupport_card_le_five ext
    (firstForeignBlock ext.block) (firstForeignBlock_ne ext.block)
  have hsecond := foreignOwnSupport_card_le_five ext
    (secondForeignBlock ext.block) (secondForeignBlock_ne ext.block)
  have hsum := selectedTailOwnDegree_eq_foreignSum ext
  have hlower := ext.tailOwnDegreeLower
  have hupper := ext.tailOwnDegreeUpper
  omega

/-! ## Every saturated foreign support is a canonical two-colour C5 -/

def encodeForeignRemainingColor
    (source target : Fin 3) (q : Fin 4) : Bool :=
  decide (q = thirdBlockRootColor source target)

def decodeForeignRemainingColor
    (source target : Fin 3) (bit : Bool) : Fin 4 :=
  if bit then thirdBlockRootColor source target else 0

theorem decode_encodeForeignRemainingColor
    (source target : Fin 3) (htarget : target ≠ source) (q : Fin 4)
    (hq : q = 0 ∨ q = thirdBlockRootColor source target) :
    decodeForeignRemainingColor source target
        (encodeForeignRemainingColor source target q) = q := by
  fin_cases source <;> fin_cases target <;> fin_cases q <;>
    simp_all [thirdBlockRootColor, encodeForeignRemainingColor,
      decodeForeignRemainingColor]

theorem encodeForeignRemainingColor_injective_on_remaining
    (source target : Fin 3) (htarget : target ≠ source)
    (q r : Fin 4)
    (hq : q = 0 ∨ q = thirdBlockRootColor source target)
    (hr : r = 0 ∨ r = thirdBlockRootColor source target)
    (hencode : encodeForeignRemainingColor source target q =
      encodeForeignRemainingColor source target r) : q = r := by
  rw [← decode_encodeForeignRemainingColor source target htarget q hq,
    ← decode_encodeForeignRemainingColor source target htarget r hr,
    hencode]

def foreignSupportBoolColoring {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (embedding : FiveVertex ↪ Fin (blockSize target)) :
    EdgeColoring FiveVertex Bool where
  color left right := encodeForeignRemainingColor ext.block target
    (tailBlockColoring
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
      (embedding left) (embedding right))
  color_symm left right := by
    exact congrArg (encodeForeignRemainingColor ext.block target)
      ((tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target).color_symm
          (embedding left) (embedding right))

theorem foreignSupportBoolColoring_noMono {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block)
    (embedding : FiveVertex ↪ Fin (blockSize target))
    (hmem : ∀ a, embedding a ∈ foreignOwnSupport ext target) :
    NoMonochromaticTriangle
      (foreignSupportBoolColoring ext target embedding) := by
  intro a b c habc hmono
  apply (tailBlockColoring_noMono
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target)
    (embedding a) (embedding b) (embedding c)
  · exact ⟨embedding.injective.ne habc.1,
      embedding.injective.ne habc.2.1,
      embedding.injective.ne habc.2.2⟩
  · constructor
    · apply encodeForeignRemainingColor_injective_on_remaining
        ext.block target htarget _ _
      · exact foreignOwnSupport_edge_color_cases ext target htarget
          (embedding a) (hmem a) (embedding b) (hmem b)
          (embedding.injective.ne habc.1)
      · exact foreignOwnSupport_edge_color_cases ext target htarget
          (embedding a) (hmem a) (embedding c) (hmem c)
          (embedding.injective.ne habc.2.1)
      · exact hmono.1
    · apply encodeForeignRemainingColor_injective_on_remaining
        ext.block target htarget _ _
      · exact foreignOwnSupport_edge_color_cases ext target htarget
          (embedding a) (hmem a) (embedding c) (hmem c)
          (embedding.injective.ne habc.2.1)
      · exact foreignOwnSupport_edge_color_cases ext target htarget
          (embedding b) (hmem b) (embedding c) (hmem c)
          (embedding.injective.ne habc.2.2)
      · exact hmono.2

/-- A saturated foreign support, together with an enumeration of all five
vertices and its checked `C5`/complement orbit. -/
structure SaturatedForeignC5 {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3) where
  targetNeSource : target ≠ ext.block
  supportCard : (foreignOwnSupport ext target).card = 5
  embedding : FiveVertex ↪ Fin (blockSize target)
  embeddingRange : Finset.univ.image embedding = foreignOwnSupport ext target
  relabel : Equiv.Perm FiveVertex
  cycleColors : ∀ left right, left ≠ right →
    tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
        (embedding (relabel left)) (embedding (relabel right)) =
      decodeForeignRemainingColor ext.block target
        (canonicalCycleWord.coloring left right)

theorem exists_saturatedForeignC5 {kind : Kind}
    (ext : FiveSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block)
    (hcard : (foreignOwnSupport ext target).card = 5) :
    Nonempty (SaturatedForeignC5 ext target) := by
  classical
  let support := foreignOwnSupport ext target
  have hcardLe : Fintype.card FiveVertex ≤ support.card := by
    simp [FiveVertex, support, hcard]
  obtain ⟨embedding, hembedding⟩ :=
    Function.Embedding.exists_of_card_le_finset hcardLe
  have hmem (a : FiveVertex) : embedding a ∈ support :=
    hembedding ⟨a, rfl⟩
  have himage : Finset.univ.image embedding = support := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
      exact hmem a
    · rw [hcard]
      rw [Finset.card_image_of_injective _ embedding.injective]
      simp [FiveVertex]
  obtain ⟨relabel, hrelabel⟩ := exists_cycle_relabel
    (foreignSupportBoolColoring ext target embedding)
    (foreignSupportBoolColoring_noMono ext target htarget embedding hmem)
  refine ⟨{
    targetNeSource := htarget
    supportCard := hcard
    embedding := embedding
    embeddingRange := by simpa [support] using himage
    relabel := relabel
    cycleColors := ?_
  }⟩
  intro left right hlr
  let q := tailBlockColoring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
      (embedding (relabel left)) (embedding (relabel right))
  have hq : q = 0 ∨ q = thirdBlockRootColor ext.block target :=
    foreignOwnSupport_edge_color_cases ext target htarget
      (embedding (relabel left)) (by simpa [support] using hmem (relabel left))
      (embedding (relabel right)) (by simpa [support] using hmem (relabel right))
      (embedding.injective.ne (relabel.injective.ne hlr))
  have hencoded : encodeForeignRemainingColor ext.block target q =
      canonicalCycleWord.coloring left right := by
    simpa [q, foreignSupportBoolColoring] using hrelabel left right hlr
  calc
    q = decodeForeignRemainingColor ext.block target
        (encodeForeignRemainingColor ext.block target q) :=
      (decode_encodeForeignRemainingColor
        ext.block target htarget q hq).symm
    _ = decodeForeignRemainingColor ext.block target
        (canonicalCycleWord.coloring left right) := by rw [hencoded]

/-! ## The combined local skeleton -/

def ForeignSizePattern {kind : Kind}
    (ext : FiveSupportExtension kind) : Prop :=
  ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 ∧
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5) ∨
    ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 4 ∧
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5) ∨
    ((foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 ∧
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 4)

def FreeSupportC5 {kind : Kind} (ext : FiveSupportExtension kind) : Prop :=
  ∃ relabel : Equiv.Perm FiveVertex, ∀ left right, left ≠ right →
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
        (relabel left) (relabel right) =
      decodeRemainingColor ext.block
        (canonicalCycleWord.coloring left right)

/-- In every five-support branch, the free support is a `C5`; the foreign
sizes have one of the three exact patterns; and every saturated foreign
part carries its own explicit `C5` witness. -/
structure LocalC5Skeleton {kind : Kind}
    (ext : FiveSupportExtension kind) : Prop where
  sizePattern : ForeignSizePattern ext
  freeSupportCycle : FreeSupportC5 ext
  firstForeignCycle :
    (foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 →
      Nonempty (SaturatedForeignC5 ext (firstForeignBlock ext.block))
  secondForeignCycle :
    (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5 →
      Nonempty (SaturatedForeignC5 ext (secondForeignBlock ext.block))

theorem localC5Skeleton {kind : Kind} (ext : FiveSupportExtension kind) :
    LocalC5Skeleton ext where
  sizePattern := foreignSupport_size_cases ext
  freeSupportCycle := ext.exists_inside_cycle_relabel
  firstForeignCycle := fun hcard =>
    exists_saturatedForeignC5 ext (firstForeignBlock ext.block)
      (firstForeignBlock_ne ext.block) hcard
  secondForeignCycle := fun hcard =>
    exists_saturatedForeignC5 ext (secondForeignBlock ext.block)
      (secondForeignBlock_ne ext.block) hcard

/-- When the selected endpoint's tail own-degree is ten, all three groups
(the free support and both foreign supports) are saturated `C5`s. -/
structure ThreeC5Skeleton {kind : Kind}
    (ext : FiveSupportExtension kind) : Type where
  tailOwnDegreeTen :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) = 10
  freeSupportCycle : FreeSupportC5 ext
  firstForeignCycle :
    SaturatedForeignC5 ext (firstForeignBlock ext.block)
  secondForeignCycle :
    SaturatedForeignC5 ext (secondForeignBlock ext.block)

theorem exists_threeC5Skeleton_of_tailOwnDegree_ten {kind : Kind}
    (ext : FiveSupportExtension kind)
    (hdegree : colorDegree
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) = 10) :
    Nonempty (ThreeC5Skeleton ext) := by
  have hfirstCap := foreignOwnSupport_card_le_five ext
    (firstForeignBlock ext.block) (firstForeignBlock_ne ext.block)
  have hsecondCap := foreignOwnSupport_card_le_five ext
    (secondForeignBlock ext.block) (secondForeignBlock_ne ext.block)
  have hsum := selectedTailOwnDegree_eq_foreignSum ext
  have hfirst :
      (foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 := by
    omega
  have hsecond :
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5 := by
    omega
  obtain ⟨firstCycle⟩ := exists_saturatedForeignC5 ext
    (firstForeignBlock ext.block) (firstForeignBlock_ne ext.block) hfirst
  obtain ⟨secondCycle⟩ := exists_saturatedForeignC5 ext
    (secondForeignBlock ext.block) (secondForeignBlock_ne ext.block) hsecond
  exact ⟨{
    tailOwnDegreeTen := hdegree
    freeSupportCycle := ext.exists_inside_cycle_relabel
    firstForeignCycle := firstCycle
    secondForeignCycle := secondCycle
  }⟩

#print axioms R4333.ProfileDHighOwnForeignC5Skeleton61.foreignOwnSupport_card_le_five
#print axioms R4333.ProfileDHighOwnForeignC5Skeleton61.selectedTailOwnDegree_eq_foreignSum
#print axioms R4333.ProfileDHighOwnForeignC5Skeleton61.foreignSupport_size_cases
#print axioms R4333.ProfileDHighOwnForeignC5Skeleton61.exists_saturatedForeignC5
#print axioms R4333.ProfileDHighOwnForeignC5Skeleton61.localC5Skeleton
#print axioms R4333.ProfileDHighOwnForeignC5Skeleton61.exists_threeC5Skeleton_of_tailOwnDegree_ten

end ProfileDHighOwnForeignC5Skeleton61
end R4333
