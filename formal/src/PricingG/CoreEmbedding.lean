import PricingG.PhysicalCoordinateColoring

namespace PricingG
open Ramsey61 Ramsey61.CEncodingCore

abbrev CoreParts := Fin 1 ⊕ (Fin 16 ⊕ Fin 16)

def coreIndex : CoreParts ≃ Fin 33 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv : Fin 16 ⊕ Fin 16 ≃ Fin 32)).trans
    (finSumFinEquiv : Fin 1 ⊕ Fin 32 ≃ Fin 33)

def coreX (i : Fin 16) : Fin 33 := ⟨1 + i.val,by omega⟩
def coreY (i : Fin 16) : Fin 33 := ⟨17 + i.val,by omega⟩

@[simp] theorem coreIndex_root : coreIndex (Sum.inl 0) = 0 := rfl
@[simp] theorem coreIndex_X (i : Fin 16) : coreIndex (Sum.inr (Sum.inl i)) = coreX i := rfl
@[simp] theorem coreIndex_Y (i : Fin 16) : coreIndex (Sum.inr (Sum.inr i)) = coreY i := by
  apply Fin.ext
  simp [coreIndex,coreY,finSumFinEquiv]
  omega

def corePartsVertex (r : Vertex) (X Y : Fin 16 ↪ Vertex) : CoreParts → Vertex :=
  Sum.elim (fun _ => r) (Sum.elim X Y)

theorem corePartsVertex_injective (c : Host) (r : Vertex) (X Y : Fin 16 ↪ Vertex)
    (hX : ∀ i, X i ∈ colorNeighborhood c (palette 0) r)
    (hY : ∀ i, Y i ∈ colorNeighborhood c (palette 1) r) :
    Function.Injective (corePartsVertex r X Y) := by
  have hx (i : Fin 16) : X i ≠ r := ((mem_colorNeighborhood _ _ _ _).mp (hX i)).1
  have hy (i : Fin 16) : Y i ≠ r := ((mem_colorNeighborhood _ _ _ _).mp (hY i)).1
  have hxy (i j : Fin 16) : X i ≠ Y j := by
    intro he
    have h0 := ((mem_colorNeighborhood _ _ _ _).mp (hX i)).2
    have h1 := ((mem_colorNeighborhood _ _ _ _).mp (hY j)).2
    rw [he] at h0
    exact (show palette 0 ≠ palette 1 by decide) (h0.symm.trans h1)
  intro a b hab
  rcases a with a | a
  · rcases b with b | (b | b)
    · congr 1; exact Subsingleton.elim _ _
    · exact False.elim (hx b hab.symm)
    · exact False.elim (hy b hab.symm)
  · rcases a with a | a
    · rcases b with b | (b | b)
      · exact False.elim (hx a hab)
      · exact congrArg (Sum.inr ∘ Sum.inl) (X.injective hab)
      · exact False.elim (hxy a b hab)
    · rcases b with b | (b | b)
      · exact False.elim (hy a hab)
      · exact False.elim (hxy b a hab.symm)
      · exact congrArg (Sum.inr ∘ Sum.inr) (Y.injective hab)

noncomputable def coreEmbedding (c : Host) (r : Vertex) (X Y : Fin 16 ↪ Vertex)
    (hX : ∀ i, X i ∈ colorNeighborhood c (palette 0) r)
    (hY : ∀ i, Y i ∈ colorNeighborhood c (palette 1) r) : Fin 33 ↪ Vertex :=
  coreIndex.symm.toEmbedding.trans ⟨corePartsVertex r X Y,corePartsVertex_injective c r X Y hX hY⟩

@[simp] theorem coreEmbedding_root (c : Host) (r : Vertex) (X Y : Fin 16 ↪ Vertex) hX hY :
    coreEmbedding c r X Y hX hY 0 = r := by
  change corePartsVertex r X Y (coreIndex.symm 0) = r
  rw [←coreIndex_root,Equiv.symm_apply_apply]
  rfl

@[simp] theorem coreEmbedding_X (c : Host) (r : Vertex) (X Y : Fin 16 ↪ Vertex) hX hY (i : Fin 16) :
    coreEmbedding c r X Y hX hY (coreX i) = X i := by
  change corePartsVertex r X Y (coreIndex.symm (coreX i)) = X i
  rw [←coreIndex_X,Equiv.symm_apply_apply]
  rfl

@[simp] theorem coreEmbedding_Y (c : Host) (r : Vertex) (X Y : Fin 16 ↪ Vertex) hX hY (i : Fin 16) :
    coreEmbedding c r X Y hX hY (coreY i) = Y i := by
  change corePartsVertex r X Y (coreIndex.symm (coreY i)) = Y i
  rw [←coreIndex_Y,Equiv.symm_apply_apply]
  rfl

/-- Every index of the literal33-vertex core is its unique physical root,
first-block vertex, or second-block vertex. -/
theorem coreIndex_cases (v : Fin 33) : v = 0 ∨ (∃ i, v = coreX i) ∨ ∃ i, v = coreY i := by
  obtain ⟨a,rfl⟩ := coreIndex.surjective v
  rcases a with a | (a | a)
  · left
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha,coreIndex_root]
  · exact Or.inr (Or.inl ⟨a,coreIndex_X a⟩)
  · exact Or.inr (Or.inr ⟨a,coreIndex_Y a⟩)

#print axioms coreEmbedding
#print axioms coreIndex_cases
end PricingG
