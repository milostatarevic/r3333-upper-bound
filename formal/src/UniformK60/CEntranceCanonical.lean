import UniformK60.CEntrancePlacement
import UniformK60.CEntranceMembership
import UniformK60.CommonWordCover

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.CEntranceCanonical
open Ramsey61 Finset UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CEntranceSource UniformK60.CEntranceLayout
open UniformK60.CommonBlocks UniformK60.CommonPairAdmission
open UniformK60.NativeSupportIndex UniformK60.NativePairCoordinates
open PricingIntegration.PairAdmission CompletionC.NativeMatrices
open UniformK60.ClassificationGeometry

abbrev layout (mode : Mode) (five : Bool) : PricingABD.ABLayout.Layout :=
  ⟨if mode=2 then .B else .A,five⟩

theorem left_size (mode : Mode) (five : Bool) :
    PricingABD.ABLayout.leftSize (layout mode five)=leftSize mode := by
  fin_cases mode <;> cases five <;> rfl

theorem right_size (mode : Mode) (five : Bool) :
    PricingABD.ABLayout.rightSize (layout mode five)=16 := by
  fin_cases mode <;> cases five <;> rfl

theorem low_free_bound (mode : Mode) (five : Bool) :
    PricingABD.ABLayout.freeSize (layout mode five)≤5 := by fin_cases mode <;> cases five <;> decide

noncomputable def leftMap {c : Host} {mode : Mode} {five : Bool}
    {t : PricingABD.ABLayout.Types} (b : Blocks c (layout mode five) t) :
    Fin (leftSize mode) ↪ Vertex :=
  (finCongr (left_size mode five).symm).toEmbedding.trans b.left.vertex

noncomputable def rightMap {c : Host} {mode : Mode} {five : Bool}
    {t : PricingABD.ABLayout.Types} (b : Blocks c (layout mode five) t) :
    Fin 16 ↪ Vertex :=
  (finCongr (right_size mode five).symm).toEmbedding.trans b.right.vertex

/-- The common word uses exactly these canonical actual60 endpoints after
simultaneous placement of the visible vertices. -/
theorem placed_matrix {c : Host} {mode : Mode} {five : Bool}
    {t : PricingABD.ABLayout.Types} (b z : Blocks c (layout mode five) t)
    (p : Fin 737) (hf : PricingABD.ABLayout.freeSize (layout mode five)=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape)
    (e : Vertex ≃ Vertex)
    (hefree : ∀ i,e (freeEmbedding (low_free_bound mode five) i)=z.free i)
    (heleft : ∀ i,e (leftVertex mode i)=leftMap z i)
    (heright : ∀ i,e (rightVertex mode i)=rightMap z i)
    (a : Fin (pairTable p).shape.dimension) :
    e (matrixVertex mode p a)=(frame z).vertex
      (supportIndex b (pairTable p).shape hf p hp a) := by
  rw [supportIndex_physical]
  unfold matrixVertex
  by_cases h0 : a.val<(pairTable p).shape.free
  · simp only [dif_pos h0,if_pos h0]
    have hi : a.val<PricingABD.ABLayout.freeSize (layout mode five) := by rw [hf];exact h0
    let i : Fin (PricingABD.ABLayout.freeSize (layout mode five)) := ⟨a.val,hi⟩
    have hv : vertex (1+a.val)=freeEmbedding (low_free_bound mode five) i := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by have := low_free_bound mode five;omega)
    rw [hv]
    exact hefree i
  · simp only [dif_neg h0,if_neg h0]
    by_cases h1 : a.val<(pairTable p).shape.free+(pairTable p).shape.left
    · simp only [dif_pos h1,if_pos h1]
      have hb := left_label_bound b (pairTable p).shape p hp
        (a.val-(pairTable p).shape.free) (by omega)
      let i : Fin (leftSize mode) := ⟨_,by rw [←left_size mode five];exact hb⟩
      exact heleft i
    · simp only [dif_neg h1,if_neg h1]
      have hb := right_label_bound b (pairTable p).shape p hp
        (a.val-(pairTable p).shape.free-(pairTable p).shape.left) (by
          have := Shape.dimension_sum (pairTable p).shape
          have := a.isLt
          omega)
      let i : Fin 16 := ⟨_,by rw [←right_size mode five];exact hb⟩
      exact heright i

end UniformK60.CEntranceCanonical
