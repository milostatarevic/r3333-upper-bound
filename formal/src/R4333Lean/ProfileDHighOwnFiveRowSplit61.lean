import R4333Lean.ProfileDFreeOwnColorColumnCap

/-!
# Five-row boundary at a high profile-D tail endpoint

A profile-D tail endpoint of own-colour degree at least fourteen has exactly
four or five free neighbours in its own colour.  This file retains five
free rows and records the resulting exhaustive split:

* in the four-support case, the first four rows are the support and the
  fifth row is outside it;
* in the five-support case, all five rows are the support, and their inside
  `K5` is the unique triangle-free two-colouring, a `C5` and its complement.

Every retained row carries the native order-61 degree floors.  No SAT or
finite-search conclusion is asserted.
-/

namespace R4333
namespace ProfileDHighOwnFiveRowSplit61

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDRowSupportBounds61
open ProfileDColumnOwnColorIncidence61
open ProfileDFreeOwnColorColumnCap

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := Fin 5

/-! ## Native five-row semantic objects -/

structure FiveExtension (kind : Kind) where
  tail : Witness kind
  inside : EdgeColoring FiveVertex (Fin 4)
  rows : FiveVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

structure DegreeFlooredFiveExtension (kind : Kind) where
  toFiveExtension : FiveExtension kind
  zeroSupportLower : ∀ a,
    11 ≤ (rowColorSupport (toFiveExtension.rows a) 0).card
  zeroSupportUpper : ∀ a,
    (rowColorSupport (toFiveExtension.rows a) 0).card ≤ 15
  nonzeroSupportLower : ∀ a q, q ≠ 0 →
    7 ≤ (rowColorSupport (toFiveExtension.rows a) q).card
  nonzeroSupportUpper : ∀ a q, q ≠ 0 →
    (rowColorSupport (toFiveExtension.rows a) q).card ≤ 13

def restrictFiveWith {kind : Kind} (ext : Extension kind)
    (embedding : FiveVertex ↪ FreeVertex) : FiveExtension kind where
  tail := ext.tail
  inside := pullbackColoring ext.inside embedding
  rows := fun a ↦ ext.rows (embedding a)
  insideNoMono :=
    noMono_pullback ext.inside embedding embedding.injective ext.insideNoMono
  insideRootForbidden := by
    intro a b hab
    exact ext.insideRootForbidden (embedding a) (embedding b)
      (embedding.injective.ne hab)
  rowsAdmissible := fun a ↦ ext.rowsAdmissible (embedding a)
  rowsPairCompatible := by
    intro a b hab x hbad
    exact ext.rowsPairCompatible (embedding a) (embedding b)
      (embedding.injective.ne hab) x hbad

def restrictDegreeFlooredFiveWith {kind : Kind} (ext : Extension kind)
    (embedding : FiveVertex ↪ FreeVertex) :
    DegreeFlooredFiveExtension kind where
  toFiveExtension := restrictFiveWith ext embedding
  zeroSupportLower := fun a ↦ row_zero_support_ge_eleven ext (embedding a)
  zeroSupportUpper := fun a ↦ row_zero_support_le_fifteen ext (embedding a)
  nonzeroSupportLower := fun a q hq ↦
    row_nonzero_support_ge_seven ext (embedding a) q hq
  nonzeroSupportUpper := fun a q hq ↦
    row_nonzero_support_le_thirteen ext (embedding a) q hq

/-! ## Appending one row outside a four-element support -/

def appendOne (embedding : Fin 4 → FreeVertex) (outside : FreeVertex) :
    FiveVertex → FreeVertex :=
  Fin.lastCases outside embedding

@[simp] theorem appendOne_last (embedding : Fin 4 → FreeVertex)
    (outside : FreeVertex) :
    appendOne embedding outside (Fin.last 4) = outside := by
  exact Fin.lastCases_last

@[simp] theorem appendOne_castSucc (embedding : Fin 4 → FreeVertex)
    (outside : FreeVertex) (a : Fin 4) :
    appendOne embedding outside a.castSucc = embedding a := by
  exact Fin.lastCases_castSucc a

theorem appendOne_injective (embedding : Fin 4 ↪ FreeVertex)
    (outside : FreeVertex) (houtside : ∀ a, embedding a ≠ outside) :
    Function.Injective (appendOne embedding outside) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
      induction y using Fin.lastCases with
      | last => rfl
      | cast y =>
          exfalso
          rw [appendOne_last, appendOne_castSucc] at hxy
          exact (houtside y) hxy.symm
  | cast x =>
      induction y using Fin.lastCases with
      | last =>
          exfalso
          rw [appendOne_castSucc, appendOne_last] at hxy
          exact (houtside x) hxy
      | cast y =>
          rw [appendOne_castSucc, appendOne_castSucc] at hxy
          exact congrArg Fin.castSucc (embedding.injective hxy)

def appendOneEmbedding (embedding : Fin 4 ↪ FreeVertex)
    (outside : FreeVertex) (houtside : ∀ a, embedding a ≠ outside) :
    FiveVertex ↪ FreeVertex where
  toFun := appendOne embedding outside
  inj' := appendOne_injective embedding outside houtside

@[simp] theorem appendOneEmbedding_last (embedding : Fin 4 ↪ FreeVertex)
    (outside : FreeVertex) (houtside : ∀ a, embedding a ≠ outside) :
    appendOneEmbedding embedding outside houtside (Fin.last 4) = outside :=
  appendOne_last embedding outside

@[simp] theorem appendOneEmbedding_castSucc
    (embedding : Fin 4 ↪ FreeVertex) (outside : FreeVertex)
    (houtside : ∀ a, embedding a ≠ outside) (a : Fin 4) :
    appendOneEmbedding embedding outside houtside a.castSucc = embedding a :=
  appendOne_castSucc embedding outside a

/-! ## The two exhaustive high-endpoint cases -/

/-- Exact decomposition of the selected tail endpoint's full own-colour
degree into its free-column support and its degree inside the 46-tail. -/
theorem selectedEndpoint_fullOwnDegree_eq_free_add_tail {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block)) :
    colorDegree (fullJoinedColoring ext) (blockRootColor block)
        (.inr (blockVertex block position.val)) =
      (freeOwnColorSupport ext block position).card +
        colorDegree ext.tail.coloring (blockRootColor block)
          (blockVertex block position.val) := by
  change colorDegree
      (joinColoring ext.inside ext.tail.coloring ext.rows)
        (blockRootColor block) (.inr (blockVertex block position.val)) = _
  rw [colorDegree_joinColoring_inr]
  rfl

/-- Using only full degree at least 14, exact free support five, and the
global per-colour cap 16 gives the preliminary tail interval `[9,11]`. -/
theorem tailOwnDegree_between_nine_eleven_of_support_five {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block position.val)))
    (hsupport : (freeOwnColorSupport ext block position).card = 5) :
    9 ≤ colorDegree ext.tail.coloring (blockRootColor block)
        (blockVertex block position.val) ∧
      colorDegree ext.tail.coloring (blockRootColor block)
        (blockVertex block position.val) ≤ 11 := by
  have hupper := fullJoinedColorDegree_le_sixteen ext
    (blockRootColor block) (.inr (blockVertex block position.val))
  rw [selectedEndpoint_fullOwnDegree_eq_free_add_tail] at hdegree hupper
  omega

/-- The analogous preliminary interval in the exact four-support case is
`[10,12]`. -/
theorem tailOwnDegree_between_ten_twelve_of_support_four {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block position.val)))
    (hsupport : (freeOwnColorSupport ext block position).card = 4) :
    10 ≤ colorDegree ext.tail.coloring (blockRootColor block)
        (blockVertex block position.val) ∧
      colorDegree ext.tail.coloring (blockRootColor block)
        (blockVertex block position.val) ≤ 12 := by
  have hupper := fullJoinedColorDegree_le_sixteen ext
    (blockRootColor block) (.inr (blockVertex block position.val))
  rw [selectedEndpoint_fullOwnDegree_eq_free_add_tail] at hdegree hupper
  omega

/-- The already-certified two-foreign-block cap improves the five-support
upper endpoint from 11 to 10. -/
theorem tailOwnDegree_between_nine_ten_of_support_five {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block position.val)))
    (hsupport : (freeOwnColorSupport ext block position).card = 5) :
    9 ≤ colorDegree ext.tail.coloring (blockRootColor block)
        (blockVertex block position.val) ∧
      colorDegree ext.tail.coloring (blockRootColor block)
        (blockVertex block position.val) ≤ 10 := by
  exact ⟨(tailOwnDegree_between_nine_eleven_of_support_five
      ext block position hdegree hsupport).1,
    tail_ownColorDegree_le_ten ext block position⟩

/-- In the four-support branch the selected tail endpoint has exactly ten
own-colour neighbours inside the 46-tail. -/
theorem tailOwnDegree_eq_ten_of_support_four {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block position.val)))
    (hsupport : (freeOwnColorSupport ext block position).card = 4) :
    colorDegree ext.tail.coloring (blockRootColor block)
        (blockVertex block position.val) = 10 := by
  have hlower := (tailOwnDegree_between_ten_twelve_of_support_four
    ext block position hdegree hsupport).1
  have hupper := tail_ownColorDegree_le_ten ext block position
  omega

structure FourSupportFiveRowExtension (kind : Kind) where
  toDegreeFlooredFiveExtension : DegreeFlooredFiveExtension kind
  block : Fin 3
  position : Fin (blockSize block)
  firstFourOwn : ∀ a : Fin 4,
    toDegreeFlooredFiveExtension.toFiveExtension.rows a.castSucc
        (blockVertex block position.val) = blockRootColor block
  fifthNotOwn :
    toDegreeFlooredFiveExtension.toFiveExtension.rows (Fin.last 4)
        (blockVertex block position.val) ≠ blockRootColor block
  /-- The high selected endpoint has exactly ten own-colour neighbours in
  the retained 46-tail. -/
  tailOwnDegreeEqTen :
    colorDegree toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val) = 10

structure FiveSupportFiveRowExtension (kind : Kind) where
  toDegreeFlooredFiveExtension : DegreeFlooredFiveExtension kind
  block : Fin 3
  position : Fin (blockSize block)
  allFiveOwn : ∀ a : FiveVertex,
    toDegreeFlooredFiveExtension.toFiveExtension.rows a
        (blockVertex block position.val) = blockRootColor block
  /-- The high selected endpoint has tail own-degree nine or ten. -/
  tailOwnDegreeLower :
    9 ≤ colorDegree
      toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val)
  tailOwnDegreeUpper :
    colorDegree toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val) ≤ 10

theorem highOwn_support_card_eq_four_or_five {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block position.val))) :
    (freeOwnColorSupport ext block position).card = 4 ∨
      (freeOwnColorSupport ext block position).card = 5 := by
  have hbounds :=
    freeOwnColorSupport_between_four_and_five_of_fullDegree_ge_fourteen
      ext block position hdegree
  omega

theorem exists_highOwnFiveRow_split {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block position.val))) :
    ((freeOwnColorSupport ext block position).card = 4 ∧
      Nonempty (FourSupportFiveRowExtension kind)) ∨
    ((freeOwnColorSupport ext block position).card = 5 ∧
      Nonempty (FiveSupportFiveRowExtension kind)) := by
  classical
  let support := freeOwnColorSupport ext block position
  rcases highOwn_support_card_eq_four_or_five ext block position hdegree with
    hfour | hfive
  · left
    have hcard : Fintype.card (Fin 4) ≤ support.card := by
      simp [support, hfour]
    obtain ⟨embeddingFour, hembeddingFour⟩ :=
      Function.Embedding.exists_of_card_le_finset hcard
    have hmemFour (a : Fin 4) : embeddingFour a ∈ support :=
      hembeddingFour ⟨a, rfl⟩
    have hexistsOutside : ∃ outside : FreeVertex, outside ∉ support := by
      by_contra hnone
      push Not at hnone
      have huniv : support = Finset.univ :=
        Finset.eq_univ_iff_forall.mpr hnone
      have hcards := congrArg Finset.card huniv
      simp [support, hfour, FreeVertex] at hcards
    obtain ⟨outside, houtside⟩ := hexistsOutside
    have hdistinct (a : Fin 4) : embeddingFour a ≠ outside := by
      intro heq
      apply houtside
      rw [← heq]
      exact hmemFour a
    let embeddingFive : FiveVertex ↪ FreeVertex :=
      appendOneEmbedding embeddingFour outside hdistinct
    let restricted := restrictDegreeFlooredFiveWith ext embeddingFive
    refine ⟨hfour, ⟨{
      toDegreeFlooredFiveExtension := restricted
      block := block
      position := position
      firstFourOwn := ?_
      fifthNotOwn := ?_
      tailOwnDegreeEqTen := ?_
    }⟩⟩
    · intro a
      change ext.rows (embeddingFive a.castSucc)
          (blockVertex block position.val) = blockRootColor block
      rw [show embeddingFive a.castSucc = embeddingFour a by
        simp [embeddingFive]]
      exact (mem_rowColorSupport _ _ _).mp (by
        simpa [support, freeOwnColorSupport] using hmemFour a)
    · change ext.rows (embeddingFive (Fin.last 4))
          (blockVertex block position.val) ≠ blockRootColor block
      rw [show embeddingFive (Fin.last 4) = outside by
        change appendOneEmbedding embeddingFour outside hdistinct
            (Fin.last 4) = outside
        exact appendOneEmbedding_last embeddingFour outside hdistinct]
      intro hcolor
      apply houtside
      exact (mem_rowColorSupport _ _ _).mpr (by
        simpa [support, freeOwnColorSupport] using hcolor)
    · simpa [restricted, restrictDegreeFlooredFiveWith,
        restrictFiveWith] using
        (tailOwnDegree_eq_ten_of_support_four
          ext block position hdegree hfour)
  · right
    have hcard : Fintype.card FiveVertex ≤ support.card := by
      simp [FiveVertex, support, hfive]
    obtain ⟨embeddingFive, hembeddingFive⟩ :=
      Function.Embedding.exists_of_card_le_finset hcard
    have hmemFive (a : FiveVertex) : embeddingFive a ∈ support :=
      hembeddingFive ⟨a, rfl⟩
    let restricted := restrictDegreeFlooredFiveWith ext embeddingFive
    refine ⟨hfive, ⟨{
      toDegreeFlooredFiveExtension := restricted
      block := block
      position := position
      allFiveOwn := ?_
      tailOwnDegreeLower := ?_
      tailOwnDegreeUpper := ?_
    }⟩⟩
    · intro a
      change ext.rows (embeddingFive a) (blockVertex block position.val) =
        blockRootColor block
      exact (mem_rowColorSupport _ _ _).mp (by
        simpa [support, freeOwnColorSupport] using hmemFive a)
    · simpa [restricted, restrictDegreeFlooredFiveWith,
        restrictFiveWith] using
        (tailOwnDegree_between_nine_ten_of_support_five
          ext block position hdegree hfive).1
    · simpa [restricted, restrictDegreeFlooredFiveWith,
        restrictFiveWith] using
        (tailOwnDegree_between_nine_ten_of_support_five
          ext block position hdegree hfive).2

/-! ## A checked canonical orbit for triangle-free two-colour K5 -/

@[ext] structure BoolK5Word where
  edge : Fin 10 → Bool
  deriving DecidableEq, Fintype, Repr

@[simp] def BoolK5Word.e01 (w : BoolK5Word) : Bool := w.edge 0
@[simp] def BoolK5Word.e02 (w : BoolK5Word) : Bool := w.edge 1
@[simp] def BoolK5Word.e03 (w : BoolK5Word) : Bool := w.edge 2
@[simp] def BoolK5Word.e04 (w : BoolK5Word) : Bool := w.edge 3
@[simp] def BoolK5Word.e12 (w : BoolK5Word) : Bool := w.edge 4
@[simp] def BoolK5Word.e13 (w : BoolK5Word) : Bool := w.edge 5
@[simp] def BoolK5Word.e14 (w : BoolK5Word) : Bool := w.edge 6
@[simp] def BoolK5Word.e23 (w : BoolK5Word) : Bool := w.edge 7
@[simp] def BoolK5Word.e24 (w : BoolK5Word) : Bool := w.edge 8
@[simp] def BoolK5Word.e34 (w : BoolK5Word) : Bool := w.edge 9

def BoolK5Word.coloring (w : BoolK5Word) :
    EdgeColoring FiveVertex Bool where
  color a b := ![
    ![false, w.e01, w.e02, w.e03, w.e04],
    ![w.e01, false, w.e12, w.e13, w.e14],
    ![w.e02, w.e12, false, w.e23, w.e24],
    ![w.e03, w.e13, w.e23, false, w.e34],
    ![w.e04, w.e14, w.e24, w.e34, false]
  ] a b
  color_symm := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl

def BoolK5Word.ofColoring (c : EdgeColoring FiveVertex Bool) : BoolK5Word :=
  ⟨![c 0 1, c 0 2, c 0 3, c 0 4, c 1 2,
     c 1 3, c 1 4, c 2 3, c 2 4, c 3 4]⟩

@[simp] theorem BoolK5Word.ofColoring_coloring (w : BoolK5Word) :
    BoolK5Word.ofColoring w.coloring = w := by
  apply BoolK5Word.ext
  funext i
  fin_cases i <;> rfl

theorem BoolK5Word.coloring_ofColoring_offDiagonal
    (c : EdgeColoring FiveVertex Bool) (a b : FiveVertex) (hab : a ≠ b) :
    (BoolK5Word.ofColoring c).coloring a b = c a b := by
  fin_cases a <;> fin_cases b <;>
    simp [BoolK5Word.ofColoring, BoolK5Word.coloring] at hab ⊢ <;>
    exact c.color_symm _ _

def BoolK5Word.relabel (w : BoolK5Word)
    (σ : Equiv.Perm FiveVertex) : BoolK5Word :=
  BoolK5Word.ofColoring (pullbackColoring w.coloring σ)

def BoolK5Word.Good (w : BoolK5Word) : Prop :=
  ¬(w.e01 = w.e02 ∧ w.e02 = w.e12) ∧
  ¬(w.e01 = w.e03 ∧ w.e03 = w.e13) ∧
  ¬(w.e01 = w.e04 ∧ w.e04 = w.e14) ∧
  ¬(w.e02 = w.e03 ∧ w.e03 = w.e23) ∧
  ¬(w.e02 = w.e04 ∧ w.e04 = w.e24) ∧
  ¬(w.e03 = w.e04 ∧ w.e04 = w.e34) ∧
  ¬(w.e12 = w.e13 ∧ w.e13 = w.e23) ∧
  ¬(w.e12 = w.e14 ∧ w.e14 = w.e24) ∧
  ¬(w.e13 = w.e14 ∧ w.e14 = w.e34) ∧
  ¬(w.e23 = w.e24 ∧ w.e24 = w.e34)

instance (w : BoolK5Word) : Decidable w.Good := by
  unfold BoolK5Word.Good
  infer_instance

theorem BoolK5Word.good_of_noMono
    (c : EdgeColoring FiveVertex Bool)
    (hnoMono : NoMonochromaticTriangle c) :
    (BoolK5Word.ofColoring c).Good := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hnoMono 0 1 2 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 0 1 3 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 0 1 4 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 0 2 3 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 0 2 4 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 0 3 4 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 1 2 3 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 1 2 4 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 1 3 4 (by simp [PairwiseDistinct]) h
  · exact fun h => hnoMono 2 3 4 (by simp [PairwiseDistinct]) h

/-- `true` edges form the cycle `0-1-2-3-4-0`. -/
def canonicalCycleWord : BoolK5Word :=
  ⟨![true, false, false, true, true,
      false, false, true, false, true]⟩

def fiveVertexPermutations : List (Equiv.Perm FiveVertex) :=
  permsOfList ([0, 1, 2, 3, 4] : List FiveVertex)

theorem mem_fiveVertexPermutations (σ : Equiv.Perm FiveVertex) :
    σ ∈ fiveVertexPermutations := by
  apply mem_permsOfList_of_mem
  intro x _
  fin_cases x <;> simp

def BoolK5Word.isCycleCovered (w : BoolK5Word) : Bool :=
  fiveVertexPermutations.any fun σ =>
    decide (w.relabel σ = canonicalCycleWord)

theorem boolK5_cycle_coverage_check :
    ∀ w : BoolK5Word, w.Good → w.isCycleCovered = true := by
  decide

theorem exists_cycle_relabel (c : EdgeColoring FiveVertex Bool)
    (hnoMono : NoMonochromaticTriangle c) :
    ∃ σ : Equiv.Perm FiveVertex, ∀ a b, a ≠ b →
      c (σ a) (σ b) = canonicalCycleWord.coloring a b := by
  let w := BoolK5Word.ofColoring c
  have hwgood : w.Good := BoolK5Word.good_of_noMono c hnoMono
  have hcovered := boolK5_cycle_coverage_check w hwgood
  simp only [BoolK5Word.isCycleCovered, List.any_eq_true] at hcovered
  obtain ⟨σ, _hσmem, hσ⟩ := hcovered
  refine ⟨σ, ?_⟩
  intro a b hab
  have hword : w.relabel σ = canonicalCycleWord := of_decide_eq_true hσ
  calc
    c (σ a) (σ b) = (w.relabel σ).coloring a b := by
      symm
      calc
        (w.relabel σ).coloring a b = w.coloring (σ a) (σ b) := by
          simpa [BoolK5Word.relabel, pullbackColoring] using
            (BoolK5Word.coloring_ofColoring_offDiagonal
              (pullbackColoring w.coloring σ) a b hab)
        _ = c (σ a) (σ b) := by
          simpa [w] using (BoolK5Word.coloring_ofColoring_offDiagonal
            c (σ a) (σ b) (σ.injective.ne hab))
    _ = canonicalCycleWord.coloring a b := by rw [hword]

/-! ## Transporting the C5 classification to the five-support case -/

def firstRemainingColor (block : Fin 3) : Fin 4 := ![2, 1, 1] block
def secondRemainingColor (block : Fin 3) : Fin 4 := ![3, 3, 2] block

def encodeRemainingColor (block : Fin 3) (q : Fin 4) : Bool :=
  decide (q = secondRemainingColor block)

def decodeRemainingColor (block : Fin 3) (bit : Bool) : Fin 4 :=
  if bit then secondRemainingColor block else firstRemainingColor block

theorem remainingColor_cases (block : Fin 3) (q : Fin 4)
    (hzero : q ≠ 0) (hown : q ≠ blockRootColor block) :
    q = firstRemainingColor block ∨ q = secondRemainingColor block := by
  fin_cases block <;> fin_cases q <;>
    simp_all [blockRootColor, firstRemainingColor, secondRemainingColor]

theorem decode_encodeRemainingColor (block : Fin 3) (q : Fin 4)
    (hq : q = firstRemainingColor block ∨
      q = secondRemainingColor block) :
    decodeRemainingColor block (encodeRemainingColor block q) = q := by
  fin_cases block <;> fin_cases q <;>
    simp_all [firstRemainingColor, secondRemainingColor,
      encodeRemainingColor, decodeRemainingColor]

theorem encodeRemainingColor_injective_on_remaining
    (block : Fin 3) (q r : Fin 4)
    (hq : q = firstRemainingColor block ∨
      q = secondRemainingColor block)
    (hr : r = firstRemainingColor block ∨
      r = secondRemainingColor block)
    (hencode : encodeRemainingColor block q =
      encodeRemainingColor block r) : q = r := by
  rw [← decode_encodeRemainingColor block q hq,
    ← decode_encodeRemainingColor block r hr, hencode]

def FiveSupportFiveRowExtension.insideBoolColoring
    {kind : Kind} (ext : FiveSupportFiveRowExtension kind) :
    EdgeColoring FiveVertex Bool where
  color a b := encodeRemainingColor ext.block
    (ext.toDegreeFlooredFiveExtension.toFiveExtension.inside a b)
  color_symm := by
    intro a b
    exact congrArg (encodeRemainingColor ext.block)
      (ext.toDegreeFlooredFiveExtension.toFiveExtension.inside.color_symm a b)

theorem FiveSupportFiveRowExtension.inside_avoids_own
    {kind : Kind} (ext : FiveSupportFiveRowExtension kind)
    (a b : FiveVertex) (hab : a ≠ b) :
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside a b ≠
      blockRootColor ext.block := by
  intro hedge
  apply ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsPairCompatible
    a b hab (blockVertex ext.block ext.position.val)
  exact ⟨hedge.trans (ext.allFiveOwn a).symm,
    (ext.allFiveOwn a).trans (ext.allFiveOwn b).symm⟩

theorem FiveSupportFiveRowExtension.inside_is_remaining
    {kind : Kind} (ext : FiveSupportFiveRowExtension kind)
    (a b : FiveVertex) (hab : a ≠ b) :
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside a b =
        firstRemainingColor ext.block ∨
      ext.toDegreeFlooredFiveExtension.toFiveExtension.inside a b =
        secondRemainingColor ext.block := by
  apply remainingColor_cases
  · exact ext.toDegreeFlooredFiveExtension.toFiveExtension.insideRootForbidden
      a b hab
  · exact ext.inside_avoids_own a b hab

theorem FiveSupportFiveRowExtension.insideBool_noMono
    {kind : Kind} (ext : FiveSupportFiveRowExtension kind) :
    NoMonochromaticTriangle ext.insideBoolColoring := by
  intro a b c habc hmono
  apply ext.toDegreeFlooredFiveExtension.toFiveExtension.insideNoMono
    a b c habc
  refine ⟨?_, ?_⟩
  · apply encodeRemainingColor_injective_on_remaining ext.block _ _
      (ext.inside_is_remaining a b habc.1)
      (ext.inside_is_remaining a c habc.2.1)
    simpa [FiveSupportFiveRowExtension.insideBoolColoring] using hmono.1
  · apply encodeRemainingColor_injective_on_remaining ext.block _ _
      (ext.inside_is_remaining a c habc.2.1)
      (ext.inside_is_remaining b c habc.2.2)
    simpa [FiveSupportFiveRowExtension.insideBoolColoring] using hmono.2

/-- The all-five-own case has one inside orbit: after permuting the retained
rows, one remaining host colour induces `C5` and the other its complement. -/
theorem FiveSupportFiveRowExtension.exists_inside_cycle_relabel
    {kind : Kind} (ext : FiveSupportFiveRowExtension kind) :
    ∃ σ : Equiv.Perm FiveVertex, ∀ a b, a ≠ b →
      ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (σ a) (σ b) =
        decodeRemainingColor ext.block
          (canonicalCycleWord.coloring a b) := by
  obtain ⟨σ, hσ⟩ := exists_cycle_relabel ext.insideBoolColoring
    ext.insideBool_noMono
  refine ⟨σ, ?_⟩
  intro a b hab
  let q := ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
    (σ a) (σ b)
  have hq : q = firstRemainingColor ext.block ∨
      q = secondRemainingColor ext.block :=
    ext.inside_is_remaining (σ a) (σ b) (σ.injective.ne hab)
  have hencoded : encodeRemainingColor ext.block q =
      canonicalCycleWord.coloring a b := by
    simpa [q, FiveSupportFiveRowExtension.insideBoolColoring] using
      hσ a b hab
  calc
    q = decodeRemainingColor ext.block
        (encodeRemainingColor ext.block q) :=
      (decode_encodeRemainingColor ext.block q hq).symm
    _ = decodeRemainingColor ext.block
        (canonicalCycleWord.coloring a b) := by
      rw [hencoded]

#print axioms R4333.ProfileDHighOwnFiveRowSplit61.restrictDegreeFlooredFiveWith
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.selectedEndpoint_fullOwnDegree_eq_free_add_tail
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.tailOwnDegree_between_nine_eleven_of_support_five
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.tailOwnDegree_between_ten_twelve_of_support_four
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.tailOwnDegree_between_nine_ten_of_support_five
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.tailOwnDegree_eq_ten_of_support_four
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.exists_highOwnFiveRow_split
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.exists_cycle_relabel
#print axioms R4333.ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension.exists_inside_cycle_relabel

end ProfileDHighOwnFiveRowSplit61
end R4333
