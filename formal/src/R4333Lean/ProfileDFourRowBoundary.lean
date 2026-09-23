import R4333Lean.ProfileDRowExtension

/-!
# Four-row boundary for the profile-D star

A full profile-D extension has fourteen vertices opposite its structured
`K15 + K15 + K16` tail.  Only four of those vertices are needed for a
finite obstruction: restricting the inside colouring and its rows to any
four vertices preserves every triangle-free, root-forbidden, admissibility,
and row-pair condition.

Consequently it is enough to refute four-row extensions for every exact tail
kind.  This is strictly weaker than classifying the full admissible-row graph
or proving that its union compatibility graph has clique number at most
three.  The universal four-row refutation remains an explicit proposition;
it is not asserted in this file.
-/

namespace R4333
namespace ProfileDFourRowBoundary

open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ColoringJoinRows

abbrev FourVertex := Fin 4

/-- The first four vertices of the omitted `Fin 14` block. -/
def fourEmbedding : FourVertex → FreeVertex :=
  Fin.castLE (by omega : 4 ≤ 14)

theorem fourEmbedding_injective : Function.Injective fourEmbedding :=
  Fin.castLE_injective (by omega : 4 ≤ 14)

/-- The exact semantic object encoded by a free-tail four-row search. -/
structure FourExtension (kind : Kind) where
  tail : Witness kind
  inside : EdgeColoring FourVertex (Fin 4)
  rows : FourVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

/-- Restrict an exact fourteen-row extension to its first four rows. -/
def restrictFour {kind : Kind} (ext : Extension kind) :
    FourExtension kind where
  tail := ext.tail
  inside := pullbackColoring ext.inside fourEmbedding
  rows := fun a ↦ ext.rows (fourEmbedding a)
  insideNoMono :=
    noMono_pullback ext.inside fourEmbedding fourEmbedding_injective
      ext.insideNoMono
  insideRootForbidden := by
    intro a b hab
    apply ext.insideRootForbidden (fourEmbedding a) (fourEmbedding b)
    exact fun h ↦ hab (fourEmbedding_injective h)
  rowsAdmissible := fun a ↦ ext.rowsAdmissible (fourEmbedding a)
  rowsPairCompatible := by
    intro a b hab x
    apply ext.rowsPairCompatible (fourEmbedding a) (fourEmbedding b)
    exact fun h ↦ hab (fourEmbedding_injective h)

/-- Every full profile-D star therefore supplies an exact four-row object. -/
def fourExtensionOfStar (w : CanonicalStarWitness ProfileD) :
    FourExtension (kindOfWitness w) :=
  restrictFour (extensionOfStar w)

theorem exists_fourExtension_of_star
    (w : CanonicalStarWitness ProfileD) :
    ∃ kind : Kind, Nonempty (FourExtension kind) :=
  ⟨kindOfWitness w, ⟨fourExtensionOfStar w⟩⟩

/-- The exact remaining finite target for this route. -/
def UniversalFourRowObstruction : Prop :=
  ∀ kind : Kind, ¬Nonempty (FourExtension kind)

/-- Refuting four-row extensions for all eight tail kinds eliminates the
entire profile-D star branch. -/
theorem no_profileD_star_of_universalFourRowObstruction
    (h : UniversalFourRowObstruction) :
    ¬Nonempty (CanonicalStarWitness ProfileD) := by
  rintro ⟨w⟩
  obtain ⟨kind, hext⟩ := exists_fourExtension_of_star w
  exact h kind hext

#print axioms R4333.ProfileDFourRowBoundary.restrictFour
#print axioms R4333.ProfileDFourRowBoundary.exists_fourExtension_of_star
#print axioms R4333.ProfileDFourRowBoundary.no_profileD_star_of_universalFourRowObstruction

end ProfileDFourRowBoundary
end R4333
