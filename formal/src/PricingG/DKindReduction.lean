import PricingG.DGenericSelectedNormalization
import PricingG.DActualRoot

namespace PricingG.DKindReduction
open R4333
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDRowExtension ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUFourSupportPositionSymmetry61 ProfileDFourRowKindSymmetry
open DGenericSelectedNormalization

abbrev DKind := ProfileDTripleJoinReduction.Kind
abbrev SelectedBranch (kind : DKind) :=
  PositionedFourSupport kind 2 (Fin.last 15) ⊕
  PositionedFiveSupport kind 2 (Fin.last 15)

def NativeKind (kind : DKind) : Prop :=
  kind = .uuu ∨ kind = .uut ∨ kind = .utu ∨ kind = .utt ∨ kind = .ttu ∨ kind = .ttt

noncomputable def swapTarget (kind : DKind) (p : Fin 16) : Fin 16 :=
  (localK16Two kind).symm p

theorem swapTarget_image (kind : DKind) (p : Fin 16) :
    tailVertexPerm kind (blockVertex 2 (swapTarget kind p).val) = blockVertex 2 p.val := by
  rw [tailVertexPerm_blockTwo]
  simp [swapTarget]

@[simp] theorem swap_own : hostColorPerm (blockRootColor 2) = blockRootColor 2 := by decide
@[simp] theorem swap_own_symm : hostColorPerm.symm (blockRootColor 2) = blockRootColor 2 := by decide

private theorem swapped_degree (kind : DKind) (tail : Witness kind) (p : Fin 16) :
    colorDegree (transportWitness tail).coloring (blockRootColor 2)
      (blockVertex 2 (swapTarget kind p).val) =
    colorDegree tail.coloring (blockRootColor 2) (blockVertex 2 p.val) := by
  change colorDegree (mapEdgeColors (relabelVertices tail.coloring (tailVertexPerm kind))
    hostColorPerm) _ _ = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices, swap_own_symm, swapTarget_image]

/-- Swap both equal K15 blocks and their host colors simultaneously, carrying
all five retained rows and their compatibility with the complete tail. -/
noncomputable def swapFour {kind : DKind} {p : Fin 16}
    (b : PositionedFourSupport kind 2 p) :
    PositionedFourSupport (swapKind kind) 2 (swapTarget kind p) where
  toDegreeFlooredFiveExtension := swapDegreeFlooredFive b.toDegreeFlooredFiveExtension
  firstFourOwn := by
    intro a
    change hostColorPerm (b.toDegreeFlooredFiveExtension.toFiveExtension.rows a.castSucc
      (tailVertexPerm kind (blockVertex 2 (swapTarget kind p).val))) = _
    rw [swapTarget_image,b.firstFourOwn,swap_own]
  fifthNotOwn := by
    change hostColorPerm (b.toDegreeFlooredFiveExtension.toFiveExtension.rows (Fin.last 4)
      (tailVertexPerm kind (blockVertex 2 (swapTarget kind p).val))) ≠ _
    rw [swapTarget_image,← swap_own]
    exact hostColorPerm.injective.ne b.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree (transportWitness b.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 2) (blockVertex 2 (swapTarget kind p).val) = 10
    rw [swapped_degree]
    exact b.tailOwnDegreeEqTen

noncomputable def swapFive {kind : DKind} {p : Fin 16}
    (b : PositionedFiveSupport kind 2 p) :
    PositionedFiveSupport (swapKind kind) 2 (swapTarget kind p) where
  toDegreeFlooredFiveExtension := swapDegreeFlooredFive b.toDegreeFlooredFiveExtension
  allFiveOwn := by
    intro a
    change hostColorPerm (b.toDegreeFlooredFiveExtension.toFiveExtension.rows a
      (tailVertexPerm kind (blockVertex 2 (swapTarget kind p).val))) = _
    rw [swapTarget_image,b.allFiveOwn,swap_own]
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree (transportWitness b.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 2) (blockVertex 2 (swapTarget kind p).val)
    rw [swapped_degree]
    exact b.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree (transportWitness b.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 2) (blockVertex 2 (swapTarget kind p).val) ≤ 10
    rw [swapped_degree]
    exact b.tailOwnDegreeUpper

noncomputable def swappedSelected {kind : DKind} : SelectedBranch kind → SelectedBranch (swapKind kind)
  | .inl b => .inl (normalizeFourSupport _ (swapFour b))
  | .inr b => .inr (normalizeFiveSupport _ (swapFive b))

/-- Eight raw template triples reduce to precisely the six retained owners;
the TU cases use the actual simultaneous color/block transport above. -/
theorem selected_branch_native (kind : DKind) (b : SelectedBranch kind) :
    ∃ k : DKind, NativeKind k ∧ Nonempty (SelectedBranch k) := by
  cases kind
  case tuu => exact ⟨.utu,by simp [NativeKind],⟨swappedSelected b⟩⟩
  case tut => exact ⟨.utt,by simp [NativeKind],⟨swappedSelected b⟩⟩
  all_goals exact ⟨_,by simp [NativeKind],⟨b⟩⟩

#print axioms swapFour
#print axioms swapFive
#print axioms selected_branch_native
end PricingG.DKindReduction
