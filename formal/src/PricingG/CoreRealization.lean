import PricingG.CoreEmbedding
import PricingIntegration.CoreLayout

namespace PricingG
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations

@[simp] theorem coreX_ne_zero (i : Fin 16) : coreX i ≠ 0 := by intro h; have := congrArg Fin.val h; simp [coreX] at this
@[simp] theorem coreY_ne_zero (i : Fin 16) : coreY i ≠ 0 := by intro h; have := congrArg Fin.val h; simp [coreY] at this
@[simp] theorem coreX_ne_Y (i j : Fin 16) : coreX i ≠ coreY j := by
  intro h; have := congrArg Fin.val h; dsimp [coreX,coreY] at this; omega
@[simp] theorem coreX_inj (i j : Fin 16) : coreX i = coreX j ↔ i = j := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [coreX] at this; omega
  · exact congrArg coreX
@[simp] theorem coreY_inj (i j : Fin 16) : coreY i = coreY j ↔ i = j := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [coreY] at this; omega
  · exact congrArg coreY

/-- This is only the disjoint physical block assembly. Its inputs are exact
pointwise equations of a particular finite base, never a case-cover premise. -/
theorem realizes_from_blocks (c : Host) (r : Vertex) (X Y : Fin 16 ↪ Vertex)
    (hX : ∀ i, X i ∈ colorNeighborhood c (palette 0) r)
    (hY : ∀ i, Y i ∈ colorNeighborhood c (palette 1) r)
    (base : CoreBase) (xx yy : Fin 16 → Fin 16 → Color)
    (b0x : ∀ i, base 0 (coreX i) = some 0) (bx0 : ∀ i, base (coreX i) 0 = some 0)
    (b0y : ∀ i, base 0 (coreY i) = some 1) (by0 : ∀ i, base (coreY i) 0 = some 1)
    (bxx : ∀ i j, i ≠ j → base (coreX i) (coreX j) = some (xx i j))
    (byy : ∀ i j, i ≠ j → base (coreY i) (coreY j) = some (yy i j))
    (byx : ∀ i j, base (coreY j) (coreX i) = base (coreX i) (coreY j))
    (hxx : ∀ i j, i ≠ j → c (X i) (X j) = palette (xx i j))
    (hyy : ∀ i j, i ≠ j → c (Y i) (Y j) = palette (yy i j))
    (hxy : ∀ i j, ∃ q, Allows (base (coreX i) (coreY j)) q ∧ c (X i) (Y j) = palette q) :
    Realizes c (coreEmbedding c r X Y hX hY) base := by
  intro u v huv
  rcases coreIndex_cases u with rfl | ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rcases coreIndex_cases v with rfl | ⟨j,rfl⟩ | ⟨j,rfl⟩
    · exact False.elim (huv rfl)
    · refine ⟨0,?_,?_⟩
      · rw [b0x]; rfl
      · simpa using ((mem_colorNeighborhood _ _ _ _).mp (hX j)).2
    · refine ⟨1,?_,?_⟩
      · rw [b0y]; rfl
      · simpa using ((mem_colorNeighborhood _ _ _ _).mp (hY j)).2
  · rcases coreIndex_cases v with rfl | ⟨j,rfl⟩ | ⟨j,rfl⟩
    · refine ⟨0,?_,?_⟩
      · rw [bx0]; rfl
      · simpa only [coreEmbedding_root,coreEmbedding_X,c.color_symm] using
          ((mem_colorNeighborhood _ _ _ _).mp (hX i)).2
    · have hij : i ≠ j := fun h => huv (congrArg coreX h)
      refine ⟨xx i j,?_,?_⟩
      · rw [bxx i j hij]; rfl
      · simpa using hxx i j hij
    · simpa using hxy i j
  · rcases coreIndex_cases v with rfl | ⟨j,rfl⟩ | ⟨j,rfl⟩
    · refine ⟨1,?_,?_⟩
      · rw [by0]; rfl
      · simpa only [coreEmbedding_root,coreEmbedding_Y,c.color_symm] using
          ((mem_colorNeighborhood _ _ _ _).mp (hY i)).2
    · obtain ⟨q,hq,hc⟩ := hxy j i
      refine ⟨q,?_,?_⟩
      · rwa [byx]
      · simpa only [coreEmbedding_X,coreEmbedding_Y,c.color_symm] using hc
    · have hij : i ≠ j := fun h => huv (congrArg coreY h)
      refine ⟨yy i j,?_,?_⟩
      · rw [byy i j hij]; rfl
      · simpa using hyy i j hij

theorem low_color_of_not_high (a : FourColor) (h0 : a ≠ palette 0) (h1 : a ≠ palette 1) :
    a = palette 2 ∨ a = palette 3 := by
  obtain ⟨q,rfl⟩ := palette_surjective a
  fin_cases q <;> simp_all

#print axioms realizes_from_blocks
end PricingG
