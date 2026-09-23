import R4333Lean.TemplateOverlap

/-!
# The finite critical-template boundary for two-root overlaps

There are exactly four possible critical neighbourhood templates: order
fifteen or sixteen, and untwisted or twisted.  This file replaces the nested
catalogue disjunction in `CriticalNeighborhoodWitness` by that four-valued
index and packages the semantic overlap of two witnesses.  It does not
enumerate embeddings or overlap normal forms.
-/

namespace R4333

open Finset

/-- The four critical three-colour templates that may occur as an attaching
neighbourhood. -/
inductive CriticalTemplateKind where
  | fifteenUntwisted
  | fifteenTwisted
  | sixteenUntwisted
  | sixteenTwisted
  deriving DecidableEq, Fintype, Repr

theorem criticalTemplateKind_card : Fintype.card CriticalTemplateKind = 4 := by
  decide

/-- The vertex type depends on whether the chosen template has order fifteen
or sixteen. -/
def CriticalTemplateVertex : CriticalTemplateKind → Type
  | .fifteenUntwisted => Fin 15
  | .fifteenTwisted => Fin 15
  | .sixteenUntwisted => Fin 16
  | .sixteenTwisted => Fin 16

instance (kind : CriticalTemplateKind) :
    Fintype (CriticalTemplateVertex kind) := by
  cases kind <;> simp only [CriticalTemplateVertex] <;> infer_instance

instance (kind : CriticalTemplateKind) :
    DecidableEq (CriticalTemplateVertex kind) := by
  cases kind <;> simp only [CriticalTemplateVertex] <;> infer_instance

/-- The order represented by a critical-template kind. -/
def criticalTemplateOrder : CriticalTemplateKind → ℕ
  | .fifteenUntwisted => 15
  | .fifteenTwisted => 15
  | .sixteenUntwisted => 16
  | .sixteenTwisted => 16

theorem criticalTemplateVertex_card (kind : CriticalTemplateKind) :
    Fintype.card (CriticalTemplateVertex kind) = criticalTemplateOrder kind := by
  cases kind <;> simp only [CriticalTemplateVertex, criticalTemplateOrder] <;>
    exact Fintype.card_fin _

/-- The explicit critical colouring selected by a kind. -/
def criticalTemplateColoring (kind : CriticalTemplateKind) :
    EdgeColoring (CriticalTemplateVertex kind) ThreeColor :=
  match kind with
  | .fifteenUntwisted => k15Untwisted
  | .fifteenTwisted => k15Twisted
  | .sixteenUntwisted => k16Untwisted
  | .sixteenTwisted => k16Twisted

/-- A critical-neighbourhood catalogue witness is equivalently a choice
among the four explicit templates, together with its order equality and weak
colour equivalence. -/
theorem criticalNeighborhoodWitness_iff_exists_kind
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V) :
    CriticalNeighborhoodWitness c hc delta root ↔
      ∃ kind : CriticalTemplateKind,
        colorDegree c delta root = criticalTemplateOrder kind ∧
        Nonempty (WeakColorEquiv
          (neighborhoodThreeColoring c hc delta root)
          (criticalTemplateColoring kind)) := by
  constructor
  · intro h
    rcases h with h15 | h16
    · obtain ⟨hdegree, t, ht, he⟩ := h15
      simp [k15CriticalCatalogue] at ht
      rcases ht with rfl | rfl
      · exact ⟨CriticalTemplateKind.fifteenUntwisted, hdegree, he⟩
      · exact ⟨CriticalTemplateKind.fifteenTwisted, hdegree, he⟩
    · obtain ⟨hdegree, t, ht, he⟩ := h16
      simp [k16CriticalCatalogue] at ht
      rcases ht with rfl | rfl
      · exact ⟨CriticalTemplateKind.sixteenUntwisted, hdegree, he⟩
      · exact ⟨CriticalTemplateKind.sixteenTwisted, hdegree, he⟩
  · rintro ⟨kind, hdegree, he⟩
    cases kind with
    | fifteenUntwisted =>
        left
        exact ⟨hdegree, k15Untwisted,
          by simp [k15CriticalCatalogue], he⟩
    | fifteenTwisted =>
        left
        exact ⟨hdegree, k15Twisted,
          by simp [k15CriticalCatalogue], he⟩
    | sixteenUntwisted =>
        right
        exact ⟨hdegree, k16Untwisted,
          by simp [k16CriticalCatalogue], he⟩
    | sixteenTwisted =>
        right
        exact ⟨hdegree, k16Twisted,
          by simp [k16CriticalCatalogue], he⟩

/-- A labeled overlap whose two template choices are exposed as elements of
the four-valued critical kind.  Thus its outer finite boundary has exactly
`4 × 4` ordered choices. -/
structure LabeledCriticalTemplateOverlap (k : ℕ) where
  leftKind : CriticalTemplateKind
  rightKind : CriticalTemplateKind
  overlap : TemplateOverlap
    (criticalTemplateColoring leftKind)
    (criticalTemplateColoring rightKind)
    (X := Fin k)

/-- Two critical neighbourhood witnesses with an intersection of exact size
`k` produce a labeled overlap between one of four left templates and one of
four right templates.  The degree equalities retain the order information
carried by the original witnesses. -/
theorem exists_labeledCriticalTemplateOverlap_of_witnesses
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (leftRoot rightRoot : V)
    (hleft : CriticalNeighborhoodWitness c hc delta leftRoot)
    (hright : CriticalNeighborhoodWitness c hc delta rightRoot)
    (hcard : #(colorNeighborhood c delta leftRoot ∩
      colorNeighborhood c delta rightRoot) = k) :
    ∃ o : LabeledCriticalTemplateOverlap k,
      colorDegree c delta leftRoot = criticalTemplateOrder o.leftKind ∧
      colorDegree c delta rightRoot = criticalTemplateOrder o.rightKind := by
  obtain ⟨leftKind, hleftDegree, ⟨leftEquiv⟩⟩ :=
    (criticalNeighborhoodWitness_iff_exists_kind
      c hc delta leftRoot).mp hleft
  obtain ⟨rightKind, hrightDegree, ⟨rightEquiv⟩⟩ :=
    (criticalNeighborhoodWitness_iff_exists_kind
      c hc delta rightRoot).mp hright
  let o : LabeledCriticalTemplateOverlap k := {
    leftKind := leftKind
    rightKind := rightKind
    overlap := labeledCommonNeighborhoodTemplateOverlap c hc delta
      leftRoot rightRoot
      (criticalTemplateColoring leftKind)
      (criticalTemplateColoring rightKind)
      hcard leftEquiv rightEquiv
  }
  exact ⟨o, hleftDegree, hrightDegree⟩

/-- The packaged overlap retains the concrete edge-colour compatibility on
every distinct pair of its `Fin k` labels. -/
theorem LabeledCriticalTemplateOverlap.compatible
    {k : ℕ} (o : LabeledCriticalTemplateOverlap k)
    (i j : Fin k) (hij : i ≠ j) :
    o.overlap.relativeColors
        (criticalTemplateColoring o.leftKind
          (o.overlap.leftVertex i) (o.overlap.leftVertex j)) =
      criticalTemplateColoring o.rightKind
        (o.overlap.rightVertex i) (o.overlap.rightVertex j) :=
  o.overlap.compatible i j hij

#print axioms R4333.criticalNeighborhoodWitness_iff_exists_kind
#print axioms R4333.exists_labeledCriticalTemplateOverlap_of_witnesses
#print axioms R4333.LabeledCriticalTemplateOverlap.compatible

end R4333
