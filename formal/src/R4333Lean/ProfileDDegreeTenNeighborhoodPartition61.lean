import R4333Lean.ProfileDDegreeTenNeighborhoodCatalogueEntrance61
import R4333Lean.CriticalK15PartitionClassification

/-!
# Exact partition normal form for a degree-ten profile-D neighbourhood

The catalogue entrance produces three disjoint five-sets in a critical
`K15`, but the weak equivalence may permute their three forbidden colours.
This file removes that bookkeeping ambiguity.  A direct six-case argument
shows that a `(5,5,5)` partition by three pairwise-distinct forbidden colours
is the canonical critical-template partition indexed by those actual
colours.  Applying it to the semantic entrance gives a completely explicit
normal form for the three `C5` supports around the selected endpoint.
-/

namespace R4333
namespace ProfileDDegreeTenNeighborhoodPartition61

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDDegreeTenNeighborhoodCatalogueEntrance61
open CriticalK15PartitionClassification

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## Palette-order-free form of the finite partition classification -/

/-- The canonical-partition theorem with the three colours supplied in an
arbitrary order.  Pairwise distinctness leaves exactly six palette orders;
each is discharged by the already checked labelled classification. -/
theorem template_partition_unique_pairwiseColors
    (twisted : Bool) (freeColor firstColor secondColor : Fin 3)
    (hcolors : PairwiseDistinct freeColor firstColor secondColor)
    (free first second : Finset (Fin 15))
    (hfreeCard : free.card = 5)
    (hfirstCard : first.card = 5)
    (hsecondCard : second.card = 5)
    (hfree : IsColorIndependentSet
      (k15Template twisted) freeColor free)
    (hfirst : IsColorIndependentSet
      (k15Template twisted) firstColor first)
    (hsecond : IsColorIndependentSet
      (k15Template twisted) secondColor second)
    (hfreeFirst : Disjoint free first)
    (hfreeSecond : Disjoint free second)
    (hfirstSecond : Disjoint first second)
    (hcover : (free ∪ first) ∪ second = Finset.univ) :
    free = canonicalPart twisted freeColor ∧
      first = canonicalPart twisted firstColor ∧
      second = canonicalPart twisted secondColor := by
  fin_cases freeColor <;> fin_cases firstColor <;> fin_cases secondColor
  all_goals try { exact (hcolors.1 rfl).elim }
  all_goals try { exact (hcolors.2.1 rfl).elim }
  all_goals try { exact (hcolors.2.2 rfl).elim }
  · exact template_partition_unique twisted free first second
      hfreeCard hfirstCard hsecondCard hfree hfirst hsecond
      hfreeFirst hfreeSecond hfirstSecond hcover
  · obtain ⟨hfree0, hsecond1, hfirst2⟩ :=
      template_partition_unique twisted free second first
        hfreeCard hsecondCard hfirstCard hfree hsecond hfirst
        hfreeSecond hfreeFirst hfirstSecond.symm (by
          simpa only [Finset.union_assoc, Finset.union_left_comm,
            Finset.union_comm] using hcover)
    exact ⟨hfree0, hfirst2, hsecond1⟩
  · obtain ⟨hfirst0, hfree1, hsecond2⟩ :=
      template_partition_unique twisted first free second
        hfirstCard hfreeCard hsecondCard hfirst hfree hsecond
        hfreeFirst.symm hfirstSecond hfreeSecond (by
          rw [Finset.union_comm first free]
          exact hcover)
    exact ⟨hfree1, hfirst0, hsecond2⟩
  · obtain ⟨hsecond0, hfree1, hfirst2⟩ :=
      template_partition_unique twisted second free first
        hsecondCard hfreeCard hfirstCard hsecond hfree hfirst
        hfreeSecond.symm hfirstSecond.symm hfreeFirst (by
          simpa only [Finset.union_assoc, Finset.union_left_comm,
            Finset.union_comm] using hcover)
    exact ⟨hfree1, hfirst2, hsecond0⟩
  · obtain ⟨hfirst0, hsecond1, hfree2⟩ :=
      template_partition_unique twisted first second free
        hfirstCard hsecondCard hfreeCard hfirst hsecond hfree
        hfirstSecond hfreeFirst.symm hfreeSecond.symm (by
          simpa only [Finset.union_assoc, Finset.union_left_comm,
            Finset.union_comm] using hcover)
    exact ⟨hfree2, hfirst0, hsecond1⟩
  · obtain ⟨hsecond0, hfirst1, hfree2⟩ :=
      template_partition_unique twisted second first free
        hsecondCard hfirstCard hfreeCard hsecond hfirst hfree
        hfirstSecond.symm hfreeSecond.symm hfreeFirst.symm (by
          simpa only [Finset.union_assoc, Finset.union_left_comm,
            Finset.union_comm] using hcover)
    exact ⟨hfree2, hfirst1, hsecond0⟩

/-! ## Application to the semantic degree-ten entrance -/

abbrev FiveSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension

abbrev ThreeC5Skeleton {kind : Kind} (ext : FiveSupportExtension kind) :=
  ProfileDHighOwnForeignC5Skeleton61.ThreeC5Skeleton ext

/-- A catalogued degree-ten neighbourhood has no remaining labelled-partition
freedom: each of its three semantic supports is the canonical maximum
independent set belonging to its transported forbidden colour. -/
theorem catalogued_supports_eq_canonical {kind : Kind}
    {ext : FiveSupportExtension kind} {skeleton : ThreeC5Skeleton ext}
    (catalogued : CataloguedDegreeTenNeighborhood ext skeleton) :
    freeLabels.image catalogued.equivalence.vertex =
        canonicalPart catalogued.twisted
          (catalogued.equivalence.colors (freeForbiddenColor ext)) ∧
      firstForeignLabels.image catalogued.equivalence.vertex =
        canonicalPart catalogued.twisted
          (catalogued.equivalence.colors
            (firstForeignForbiddenColor ext)) ∧
      secondForeignLabels.image catalogued.equivalence.vertex =
        canonicalPart catalogued.twisted
          (catalogued.equivalence.colors
            (secondForeignForbiddenColor ext)) := by
  exact template_partition_unique_pairwiseColors
    catalogued.twisted
    (catalogued.equivalence.colors (freeForbiddenColor ext))
    (catalogued.equivalence.colors (firstForeignForbiddenColor ext))
    (catalogued.equivalence.colors (secondForeignForbiddenColor ext))
    catalogued.templateForbiddenColorsPairwiseDistinct
    (freeLabels.image catalogued.equivalence.vertex)
    (firstForeignLabels.image catalogued.equivalence.vertex)
    (secondForeignLabels.image catalogued.equivalence.vertex)
    catalogued.freeTemplateCard
    catalogued.firstForeignTemplateCard
    catalogued.secondForeignTemplateCard
    catalogued.freeTemplateIndependent
    catalogued.firstForeignTemplateIndependent
    catalogued.secondForeignTemplateIndependent
    catalogued.freeTemplateDisjointFirstForeign
    catalogued.freeTemplateDisjointSecondForeign
    catalogued.firstForeignTemplateDisjointSecondForeign
    catalogued.templateCover

/-- Existential semantic form, obtained directly from every degree-ten
three-`C5` skeleton. -/
theorem exists_exactPartitionNormalForm {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    ∃ catalogued : CataloguedDegreeTenNeighborhood ext skeleton,
      freeLabels.image catalogued.equivalence.vertex =
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors (freeForbiddenColor ext)) ∧
        firstForeignLabels.image catalogued.equivalence.vertex =
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors
              (firstForeignForbiddenColor ext)) ∧
        secondForeignLabels.image catalogued.equivalence.vertex =
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors
              (secondForeignForbiddenColor ext)) := by
  obtain ⟨catalogued⟩ := exists_cataloguedDegreeTenNeighborhood skeleton
  exact ⟨catalogued, catalogued_supports_eq_canonical catalogued⟩

#print axioms template_partition_unique_pairwiseColors
#print axioms catalogued_supports_eq_canonical
#print axioms exists_exactPartitionNormalForm

end ProfileDDegreeTenNeighborhoodPartition61
end R4333
