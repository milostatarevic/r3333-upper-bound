import R4333Lean.CriticalTemplateDeletion
import R4333Lean.K15Extension

/-!
# Restricting critical K16 isomorphisms to K15

The two certified K16 templates are vertex transitive.  Thus, after moving
the image of the added vertex to label 15, a weak colour isomorphism of a
one-vertex extension restricts to a weak colour isomorphism of the original
K15 with the fixed deletion of the same template.
-/

namespace R4333

/-- Restrict a permutation of `Fin (n+1)` fixing its last point to the first
`n` points. -/
def restrictLastMap {n : Nat} (e : Fin (n + 1) ≃ Fin (n + 1))
    (hfix : e (Fin.last n) = Fin.last n) (i : Fin n) : Fin n :=
  (e i.castSucc).castPred (by
    rw [← hfix]
    exact e.injective.ne (Fin.castSucc_ne_last i))

@[simp]
theorem restrictLastMap_castSucc {n : Nat}
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (hfix : e (Fin.last n) = Fin.last n) (i : Fin n) :
    (restrictLastMap e hfix i).castSucc = e i.castSucc := by
  apply Fin.castSucc_castPred

theorem restrictLastMap_injective {n : Nat}
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (hfix : e (Fin.last n) = Fin.last n) :
    Function.Injective (restrictLastMap e hfix) := by
  intro i j hij
  apply Fin.castSucc_injective
  apply e.injective
  rw [← restrictLastMap_castSucc e hfix i,
    ← restrictLastMap_castSucc e hfix j, hij]

noncomputable def restrictLastEquiv {n : Nat}
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (hfix : e (Fin.last n) = Fin.last n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (restrictLastMap e hfix)
    ((Fintype.bijective_iff_injective_and_card
      (restrictLastMap e hfix)).mpr
        ⟨restrictLastMap_injective e hfix, rfl⟩)

@[simp]
theorem restrictLastEquiv_apply {n : Nat}
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (hfix : e (Fin.last n) = Fin.last n) (i : Fin n) :
    restrictLastEquiv e hfix i = restrictLastMap e hfix i := rfl

@[simp]
theorem restrictLastEquiv_castSucc {n : Nat}
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (hfix : e (Fin.last n) = Fin.last n) (i : Fin n) :
    (restrictLastEquiv e hfix i).castSucc = e i.castSucc := by
  exact restrictLastMap_castSucc e hfix i

/-- A template automorphism that sends a selected vertex to the last one,
viewed as a weak colour isomorphism with the identity colour map. -/
noncomputable def k16TemplateToLastWeakEquiv
    (twisted : Bool) (deleted : Fin 16) :
    WeakColorEquiv (k16Template twisted) (k16Template twisted) where
  vertex := k16TemplateToLastEquiv twisted deleted
  colors := Equiv.refl ThreeColor
  map_color := by
    intro u v huv
    simpa using k16TemplateToLastMap_preserves twisted deleted u v huv

/-- A weak isomorphism from the canonical extension of a good K15 to one of
the critical K16 templates restricts to the corresponding fixed K15
template. -/
noncomputable def restrictCriticalK15WeakEquiv
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (twisted : Bool)
    (e : WeakColorEquiv (extendCriticalK15 c hc) (k16Template twisted)) :
    WeakColorEquiv c (k15Template twisted) := by
  let deleted : Fin 16 := e.vertex (Fin.last 15)
  let f : WeakColorEquiv (extendCriticalK15 c hc) (k16Template twisted) :=
    e.trans (k16TemplateToLastWeakEquiv twisted deleted)
  have hfix : f.vertex (Fin.last 15) = Fin.last 15 := by
    change k16TemplateToLastMap twisted deleted deleted = Fin.last 15
    exact k16TemplateToLastMap_deleted twisted deleted
  exact {
    vertex := restrictLastEquiv f.vertex hfix
    colors := f.colors
    map_color := by
      intro i j hij
      have h := f.map_color i.castSucc j.castSucc
        (by
          intro hcast
          exact hij (Fin.castSucc_injective 15 hcast))
      cases twisted
      · change f.colors (c i j) =
          k16Untwisted
            (restrictLastEquiv f.vertex hfix i).castSucc
            (restrictLastEquiv f.vertex hfix j).castSucc
        rw [restrictLastEquiv_castSucc, restrictLastEquiv_castSucc]
        simpa [extendCriticalK15, k16Template] using h
      · change f.colors (c i j) =
          k16Twisted
            (restrictLastEquiv f.vertex hfix i).castSucc
            (restrictLastEquiv f.vertex hfix j).castSucc
        rw [restrictLastEquiv_castSucc, restrictLastEquiv_castSucc]
        simpa [extendCriticalK15, k16Template] using h
  }

#print axioms R4333.restrictLastMap_injective
#print axioms R4333.restrictCriticalK15WeakEquiv

end R4333
