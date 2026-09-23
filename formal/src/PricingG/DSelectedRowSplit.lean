import R4333Lean.ProfileDHighOwnFiveRowSplit61

namespace PricingG.DSelectedRowSplit
open R4333 R4333.ColoringJoinRows R4333.ProfileDTripleJoinReduction
open R4333.ProfileDRowExtension R4333.ProfileDRowSupportBounds61
open R4333.ProfileDColumnOwnColorIncidence61 R4333.ProfileDFreeOwnColorColumnCap
open R4333.ProfileDHighOwnFiveRowSplit61

/-- Strengthens the retained semantic split by preserving its selected
physical block and endpoint index in the theorem's result. The original
construction is reused verbatim except for these two explicit equalities. -/
theorem exists_selected_high_row_split {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block position.val))) :
    ((freeOwnColorSupport ext block position).card = 4 ∧
      (∃ b : FourSupportFiveRowExtension kind, b.block = block ∧ b.position.val = position.val)) ∨
    ((freeOwnColorSupport ext block position).card = 5 ∧
      (∃ b : FiveSupportFiveRowExtension kind, b.block = block ∧ b.position.val = position.val)) := by
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
    refine ⟨hfour, {
      toDegreeFlooredFiveExtension := restricted
      block := block
      position := position
      firstFourOwn := ?_
      fifthNotOwn := ?_
      tailOwnDegreeEqTen := ?_
    }, rfl, rfl⟩
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
    refine ⟨hfive, {
      toDegreeFlooredFiveExtension := restricted
      block := block
      position := position
      allFiveOwn := ?_
      tailOwnDegreeLower := ?_
      tailOwnDegreeUpper := ?_
    }, rfl, rfl⟩
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


#print axioms exists_selected_high_row_split
end PricingG.DSelectedRowSplit
