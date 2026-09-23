import R4333Lean.CriticalTemplateDeletion

/-!
# Explicit full palette symmetry of the critical K15/K16 templates

Every permutation of the three template colours is induced by a vertex
permutation, for both critical types and both orders.  This finite fact is
what permits each root-neighbourhood palette in the single-root reduction to
be normalized independently.  The 24 maps below are checked directly in the
kernel against `CriticalTemplates.lean`.
-/

namespace R4333

/-- The six permutations of `Fin 3`, in lexicographic image order. -/
def criticalPaletteColorMap : Fin 6 → ThreeColor → ThreeColor := ![
  ![0, 1, 2],
  ![0, 2, 1],
  ![1, 0, 2],
  ![1, 2, 0],
  ![2, 0, 1],
  ![2, 1, 0]
]

set_option maxRecDepth 100000 in
theorem criticalPaletteColorMap_bijective (code : Fin 6) :
    Function.Bijective (criticalPaletteColorMap code) := by
  fin_cases code <;> decide

noncomputable def criticalPaletteColorEquiv (code : Fin 6) :
    ThreeColor ≃ ThreeColor :=
  Equiv.ofBijective (criticalPaletteColorMap code)
    (criticalPaletteColorMap_bijective code)

@[simp] theorem criticalPaletteColorEquiv_apply
    (code : Fin 6) (q : ThreeColor) :
    criticalPaletteColorEquiv code q = criticalPaletteColorMap code q := rfl

/-- Recover the lexicographic code of an arbitrary three-colour equivalence. -/
def criticalPaletteCode (e : ThreeColor ≃ ThreeColor) : Fin 6 :=
  if e 0 = 0 then
    if e 1 = 1 then 0 else 1
  else if e 0 = 1 then
    if e 1 = 0 then 2 else 3
  else if e 1 = 0 then 4 else 5

set_option maxRecDepth 100000 in
theorem criticalPaletteColorEquiv_code
    (e : ThreeColor ≃ ThreeColor) :
    criticalPaletteColorEquiv (criticalPaletteCode e) = e := by
  classical
  revert e
  decide

/-! ## The twelve order-15 vertex maps -/

def k15UntwistedPaletteVertexMap : Fin 6 → Fin 15 → Fin 15 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
  ![0, 8, 6, 14, 11, 3, 13, 5, 10, 2, 12, 4, 1, 9, 7],
  ![2, 1, 14, 13, 7, 4, 11, 8, 5, 6, 9, 10, 0, 3, 12],
  ![2, 0, 6, 4, 10, 8, 14, 12, 1, 3, 5, 7, 9, 11, 13],
  ![1, 4, 14, 11, 3, 6, 12, 9, 7, 2, 8, 13, 5, 0, 10],
  ![1, 5, 2, 6, 13, 9, 14, 10, 4, 0, 7, 3, 8, 12, 11]
]

def k15TwistedPaletteVertexMap : Fin 6 → Fin 15 → Fin 15 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
  ![7, 8, 1, 14, 10, 5, 12, 3, 11, 4, 13, 2, 6, 9, 0],
  ![1, 3, 9, 11, 7, 12, 6, 13, 10, 8, 2, 0, 5, 14, 4],
  ![4, 9, 0, 13, 8, 12, 5, 1, 3, 14, 7, 10, 6, 2, 11],
  ![2, 7, 13, 8, 0, 6, 12, 10, 4, 1, 11, 14, 5, 3, 9],
  ![9, 13, 14, 10, 1, 6, 5, 2, 7, 3, 0, 4, 12, 11, 8]
]

def k15PaletteVertexMap
    (twisted : Bool) (code : Fin 6) : Fin 15 → Fin 15 :=
  if twisted then k15TwistedPaletteVertexMap code
  else k15UntwistedPaletteVertexMap code

set_option maxRecDepth 100000 in
theorem k15PaletteVertexMap_bijective
    (twisted : Bool) (code : Fin 6) :
    Function.Bijective (k15PaletteVertexMap twisted code) := by
  cases twisted <;> fin_cases code <;> decide

noncomputable def k15PaletteVertexEquiv
    (twisted : Bool) (code : Fin 6) : Fin 15 ≃ Fin 15 :=
  Equiv.ofBijective (k15PaletteVertexMap twisted code)
    (k15PaletteVertexMap_bijective twisted code)

@[simp] theorem k15PaletteVertexEquiv_apply
    (twisted : Bool) (code : Fin 6) (x : Fin 15) :
    k15PaletteVertexEquiv twisted code x =
      k15PaletteVertexMap twisted code x := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15PaletteVertexMap_preserves
    (twisted : Bool) (code : Fin 6) :
    ∀ u v, u ≠ v →
      k15Template twisted
          (k15PaletteVertexMap twisted code u)
          (k15PaletteVertexMap twisted code v) =
        criticalPaletteColorMap code (k15Template twisted u v) := by
  cases twisted <;> fin_cases code <;> decide

/-! ## The twelve order-16 vertex maps -/

def k16UntwistedPaletteVertexMap : Fin 6 → Fin 16 → Fin 16 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  ![0, 1, 4, 5, 3, 2, 7, 6, 12, 13, 8, 9, 15, 14, 11, 10],
  ![0, 2, 8, 10, 6, 4, 14, 12, 11, 9, 3, 1, 13, 15, 5, 7],
  ![0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13],
  ![0, 4, 8, 12, 3, 7, 11, 15, 6, 2, 14, 10, 5, 1, 13, 9],
  ![0, 4, 3, 7, 12, 8, 15, 11, 5, 1, 6, 2, 9, 13, 10, 14]
]

def k16TwistedPaletteVertexMap : Fin 6 → Fin 16 → Fin 16 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  ![0, 12, 5, 9, 7, 11, 2, 14, 15, 3, 10, 6, 8, 4, 13, 1],
  ![0, 2, 8, 10, 5, 14, 4, 15, 11, 9, 3, 1, 7, 12, 6, 13],
  ![0, 7, 14, 9, 15, 1, 8, 6, 13, 10, 3, 4, 11, 5, 12, 2],
  ![0, 5, 15, 10, 11, 13, 7, 1, 6, 3, 9, 12, 14, 8, 2, 4],
  ![0, 4, 7, 3, 8, 15, 12, 11, 14, 10, 9, 13, 5, 2, 1, 6]
]

def k16PaletteVertexMap
    (twisted : Bool) (code : Fin 6) : Fin 16 → Fin 16 :=
  if twisted then k16TwistedPaletteVertexMap code
  else k16UntwistedPaletteVertexMap code

set_option maxRecDepth 100000 in
theorem k16PaletteVertexMap_bijective
    (twisted : Bool) (code : Fin 6) :
    Function.Bijective (k16PaletteVertexMap twisted code) := by
  cases twisted <;> fin_cases code <;> decide

noncomputable def k16PaletteVertexEquiv
    (twisted : Bool) (code : Fin 6) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (k16PaletteVertexMap twisted code)
    (k16PaletteVertexMap_bijective twisted code)

@[simp] theorem k16PaletteVertexEquiv_apply
    (twisted : Bool) (code : Fin 6) (x : Fin 16) :
    k16PaletteVertexEquiv twisted code x =
      k16PaletteVertexMap twisted code x := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16PaletteVertexMap_preserves
    (twisted : Bool) (code : Fin 6) :
    ∀ u v, u ≠ v →
      k16Template twisted
          (k16PaletteVertexMap twisted code u)
          (k16PaletteVertexMap twisted code v) =
        criticalPaletteColorMap code (k16Template twisted u v) := by
  cases twisted <;> fin_cases code <;> decide

/-! ## Arbitrary-palette endpoints -/

theorem k15Template_fullPaletteSymmetry
    (twisted : Bool) (e : ThreeColor ≃ ThreeColor) :
    ∃ vertex : Fin 15 ≃ Fin 15,
      ∀ u v, u ≠ v →
        k15Template twisted (vertex u) (vertex v) =
          e (k15Template twisted u v) := by
  let code := criticalPaletteCode e
  refine ⟨k15PaletteVertexEquiv twisted code, ?_⟩
  intro u v huv
  rw [k15PaletteVertexEquiv_apply]
  have h := k15PaletteVertexMap_preserves twisted code u v huv
  rw [← criticalPaletteColorEquiv_apply] at h
  rw [criticalPaletteColorEquiv_code] at h
  exact h

theorem k16Template_fullPaletteSymmetry
    (twisted : Bool) (e : ThreeColor ≃ ThreeColor) :
    ∃ vertex : Fin 16 ≃ Fin 16,
      ∀ u v, u ≠ v →
        k16Template twisted (vertex u) (vertex v) =
          e (k16Template twisted u v) := by
  let code := criticalPaletteCode e
  refine ⟨k16PaletteVertexEquiv twisted code, ?_⟩
  intro u v huv
  rw [k16PaletteVertexEquiv_apply]
  have h := k16PaletteVertexMap_preserves twisted code u v huv
  rw [← criticalPaletteColorEquiv_apply] at h
  rw [criticalPaletteColorEquiv_code] at h
  exact h

#print axioms R4333.criticalPaletteColorEquiv_code
#print axioms R4333.k15PaletteVertexMap_preserves
#print axioms R4333.k16PaletteVertexMap_preserves
#print axioms R4333.k15Template_fullPaletteSymmetry
#print axioms R4333.k16Template_fullPaletteSymmetry

end R4333
