import R4333Lean.CriticalTemplateShadowLaws
import R4333Lean.SharedCriticalCompletion

/-!
# Intersections of maximum independent sets in the critical templates

The local attaching-set argument uses one small finite fact repeatedly: two
five-vertex independent sets in the same colour of a critical K15 or K16
template meet in zero, two, or five vertices.  This file proves that fact
from the explicit checked templates.

For K16, every maximum independent set already has a unique shadow.  For
K15, we lift the set through the canonical deletion embedding into K16 and
apply the same shadow theorem.  The remaining neighbourhood-intersection
calculation is a direct finite theorem over the two explicit K16 templates.
-/

namespace R4333

set_option maxRecDepth 100000 in
/-- The exact common-neighbourhood intersection spectrum in either critical
K16 template. -/
theorem k16Template_sameColorNeighborhood_intersection_card
    (twisted : Bool) (q : ThreeColor) (left right : Fin 16) :
    (colorNeighborhood (k16Template twisted) q left ∩
        colorNeighborhood (k16Template twisted) q right).card ∈
      ({0, 2, 5} : Finset Nat) := by
  cases twisted <;> fin_cases q <;> fin_cases left <;> fin_cases right <;>
    decide

/-- Two same-colour maximum independent sets in a critical K16 template
have intersection order zero, two, or five. -/
theorem k16Template_maxIndependentSets_intersection_card
    (twisted : Bool) (q : ThreeColor) (left right : Finset (Fin 16))
    (hleftCard : left.card = 5) (hrightCard : right.card = 5)
    (hleftIndependent :
      IsColorIndependentSet (k16Template twisted) q left)
    (hrightIndependent :
      IsColorIndependentSet (k16Template twisted) q right) :
    (left ∩ right).card ∈ ({0, 2, 5} : Finset Nat) := by
  obtain ⟨leftShadow, hleft, _⟩ :=
    k16Template_maxIndependentSet_unique_shadow
      twisted q left hleftCard hleftIndependent
  obtain ⟨rightShadow, hright, _⟩ :=
    k16Template_maxIndependentSet_unique_shadow
      twisted q right hrightCard hrightIndependent
  rw [hleft, hright]
  exact k16Template_sameColorNeighborhood_intersection_card
    twisted q leftShadow rightShadow

/-- Canonically regard a set of labels in the deleted K15 template as a set
of labels in its K16 completion. -/
def liftK15Finset (S : Finset (Fin 15)) : Finset (Fin 16) :=
  S.image Fin.castSucc

@[simp] theorem liftK15Finset_card (S : Finset (Fin 15)) :
    (liftK15Finset S).card = S.card := by
  simp [liftK15Finset, Finset.card_image_of_injective,
    Fin.castSucc_injective]

theorem liftK15Finset_inter (left right : Finset (Fin 15)) :
    liftK15Finset (left ∩ right) =
      liftK15Finset left ∩ liftK15Finset right := by
  simpa [liftK15Finset] using
    (Finset.image_inter left right (Fin.castSucc_injective 15))

theorem k15Template_edge_eq_k16Template
    (twisted : Bool) (left right : Fin 15) :
    k15Template twisted left right =
      k16Template twisted left.castSucc right.castSucc := by
  cases twisted <;> rfl

theorem liftK15Finset_independent
    (twisted : Bool) (q : ThreeColor) (S : Finset (Fin 15))
    (hS : IsColorIndependentSet (k15Template twisted) q S) :
    IsColorIndependentSet (k16Template twisted) q (liftK15Finset S) := by
  intro x hx y hy hxy
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.mp hy
  have hxy0 : x0 ≠ y0 := fun h => hxy (congrArg Fin.castSucc h)
  simpa [k15Template_edge_eq_k16Template] using hS x0 hx0 y0 hy0 hxy0

/-- The corresponding maximum-set intersection spectrum in either critical
K15 deletion. -/
theorem k15Template_maxIndependentSets_intersection_card
    (twisted : Bool) (q : ThreeColor) (left right : Finset (Fin 15))
    (hleftCard : left.card = 5) (hrightCard : right.card = 5)
    (hleftIndependent :
      IsColorIndependentSet (k15Template twisted) q left)
    (hrightIndependent :
      IsColorIndependentSet (k15Template twisted) q right) :
    (left ∩ right).card ∈ ({0, 2, 5} : Finset Nat) := by
  have hlift := k16Template_maxIndependentSets_intersection_card
    twisted q (liftK15Finset left) (liftK15Finset right)
    (by simpa using hleftCard) (by simpa using hrightCard)
    (liftK15Finset_independent twisted q left hleftIndependent)
    (liftK15Finset_independent twisted q right hrightIndependent)
  rw [← liftK15Finset_inter] at hlift
  simpa using hlift

/-- Uniform form covering all four checked critical templates. -/
theorem criticalTemplate_maxIndependentSets_intersection_card
    (kind : CriticalTemplateKind) (q : ThreeColor)
    (left right : Finset (CriticalTemplateVertex kind))
    (hleftCard : left.card = 5) (hrightCard : right.card = 5)
    (hleftIndependent :
      IsColorIndependentSet (criticalTemplateColoring kind) q left)
    (hrightIndependent :
      IsColorIndependentSet (criticalTemplateColoring kind) q right) :
    (left ∩ right).card ∈ ({0, 2, 5} : Finset Nat) := by
  cases kind with
  | fifteenUntwisted =>
      change IsColorIndependentSet k15Untwisted q left at hleftIndependent
      change IsColorIndependentSet k15Untwisted q right at hrightIndependent
      exact k15Template_maxIndependentSets_intersection_card false q
        left right hleftCard hrightCard
        (by simpa [k15Template] using hleftIndependent)
        (by simpa [k15Template] using hrightIndependent)
  | fifteenTwisted =>
      change IsColorIndependentSet k15Twisted q left at hleftIndependent
      change IsColorIndependentSet k15Twisted q right at hrightIndependent
      exact k15Template_maxIndependentSets_intersection_card true q
        left right hleftCard hrightCard
        (by simpa [k15Template] using hleftIndependent)
        (by simpa [k15Template] using hrightIndependent)
  | sixteenUntwisted =>
      change IsColorIndependentSet k16Untwisted q left at hleftIndependent
      change IsColorIndependentSet k16Untwisted q right at hrightIndependent
      exact k16Template_maxIndependentSets_intersection_card false q
        left right hleftCard hrightCard
        (by simpa [k16Template] using hleftIndependent)
        (by simpa [k16Template] using hrightIndependent)
  | sixteenTwisted =>
      change IsColorIndependentSet k16Twisted q left at hleftIndependent
      change IsColorIndependentSet k16Twisted q right at hrightIndependent
      exact k16Template_maxIndependentSets_intersection_card true q
        left right hleftCard hrightCard
        (by simpa [k16Template] using hleftIndependent)
        (by simpa [k16Template] using hrightIndependent)

namespace WeakColorEquiv

/-- A weak colour equivalence transports a finite independent set. -/
theorem image_isColorIndependentSet
    {V W C D : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [DecidableEq C] [DecidableEq D]
    {c : EdgeColoring V C} {d : EdgeColoring W D}
    (e : WeakColorEquiv c d) (q : C) (S : Finset V)
    (hS : IsColorIndependentSet c q S) :
    IsColorIndependentSet d (e.colors q) (S.image e.vertex) := by
  intro x hx y hy hxy
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.mp hy
  have hxy0 : x0 ≠ y0 := fun h => hxy (congrArg e.vertex h)
  intro hcolor
  apply hS x0 hx0 y0 hy0 hxy0
  apply e.colors.injective
  calc
    e.colors (c x0 y0) = d (e.vertex x0) (e.vertex y0) :=
      e.map_color x0 y0 hxy0
    _ = e.colors q := hcolor

/-- The intersection spectrum of two maximum independent sets transports
through a weak equivalence into any one of the four critical templates. -/
theorem maximumIndependentSets_intersection_card
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    {c : EdgeColoring V C}
    (kind : CriticalTemplateKind)
    (e : WeakColorEquiv c (criticalTemplateColoring kind))
    (q : C) (left right : Finset V)
    (hleftCard : left.card = 5) (hrightCard : right.card = 5)
    (hleftIndependent : IsColorIndependentSet c q left)
    (hrightIndependent : IsColorIndependentSet c q right) :
    (left ∩ right).card ∈ ({0, 2, 5} : Finset Nat) := by
  have hcritical := criticalTemplate_maxIndependentSets_intersection_card
    kind (e.colors q) (left.image e.vertex) (right.image e.vertex)
    ((Finset.card_image_of_injective _ e.vertex.injective).trans hleftCard)
    ((Finset.card_image_of_injective _ e.vertex.injective).trans hrightCard)
    (e.image_isColorIndependentSet q left hleftIndependent)
    (e.image_isColorIndependentSet q right hrightIndependent)
  have hinter :
      (left ∩ right).image e.vertex =
        left.image e.vertex ∩ right.image e.vertex := by
    exact Finset.image_inter left right e.vertex.injective
  rw [← hinter] at hcritical
  have hcardInter : ((left ∩ right).image e.vertex).card =
      (left ∩ right).card :=
    Finset.card_image_of_injective _ e.vertex.injective
  rw [hcardInter] at hcritical
  exact hcritical

end WeakColorEquiv

/-- Host-level form for an actual degree-15/16 monochromatic neighbourhood
with its checked shared critical completion. -/
theorem SharedCriticalCompletion.maximumIndependentSets_intersection_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {q : FourColor} {root : V}
    (completion : SharedCriticalCompletion c hc q root)
    (r : NeighborhoodColor q)
    (left right : Finset (NeighborhoodVertex c q root))
    (hleftCard : left.card = 5) (hrightCard : right.card = 5)
    (hleftIndependent : IsColorIndependentSet
      (neighborhoodThreeColoring c hc q root) r left)
    (hrightIndependent : IsColorIndependentSet
      (neighborhoodThreeColoring c hc q root) r right) :
    (left ∩ right).card ∈ ({0, 2, 5} : Finset Nat) :=
  completion.weakEquiv.maximumIndependentSets_intersection_card
    completion.kind r left right hleftCard hrightCard
      hleftIndependent hrightIndependent

#print axioms R4333.k16Template_sameColorNeighborhood_intersection_card
#print axioms R4333.k16Template_maxIndependentSets_intersection_card
#print axioms R4333.k15Template_maxIndependentSets_intersection_card
#print axioms R4333.criticalTemplate_maxIndependentSets_intersection_card
#print axioms R4333.SharedCriticalCompletion.maximumIndependentSets_intersection_card

end R4333
