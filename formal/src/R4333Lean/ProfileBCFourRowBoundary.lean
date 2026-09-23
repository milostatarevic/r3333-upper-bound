import R4333Lean.ProfileBRowExtension
import R4333Lean.ProfileCRowExtension

/-!
# Four-row boundaries for profiles B and C

The omitted block has thirteen vertices in profile B and fourteen in profile
C.  Restricting either exact row extension to four vertices preserves all
conditions.  Therefore the two full star branches reduce to universal
four-row obstructions over their exact structured tails.

The universal propositions are left explicit and unproved here.
-/

namespace R4333

namespace ProfileBFourRowBoundary

open SingleRootStarCNF
open ProfileBRowExtension
open ColoringJoinRows

abbrev FourVertex := Fin 4

def fourEmbedding : FourVertex → FreeVertex :=
  Fin.castLE (by omega : 4 ≤ 13)

theorem fourEmbedding_injective : Function.Injective fourEmbedding :=
  Fin.castLE_injective (by omega : 4 ≤ 13)

structure FourExtension (kind : Kind) where
  tail : TailWitness kind
  inside : EdgeColoring FourVertex (Fin 4)
  rows : FourVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

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

def fourExtensionOfStar (w : CanonicalStarWitness ProfileB) :
    FourExtension (kindOfWitness w) :=
  restrictFour (extensionOfStar w)

def UniversalFourRowObstruction : Prop :=
  ∀ kind : Kind, ¬Nonempty (FourExtension kind)

theorem no_profileB_star_of_universalFourRowObstruction
    (h : UniversalFourRowObstruction) :
    ¬Nonempty (CanonicalStarWitness ProfileB) := by
  rintro ⟨w⟩
  exact h (kindOfWitness w) ⟨fourExtensionOfStar w⟩

#print axioms R4333.ProfileBFourRowBoundary.restrictFour
#print axioms R4333.ProfileBFourRowBoundary.no_profileB_star_of_universalFourRowObstruction

end ProfileBFourRowBoundary

namespace ProfileCFourRowBoundary

open SingleRootStarCNF
open ProfileCRowExtension
open ColoringJoinRows

abbrev FourVertex := Fin 4

def fourEmbedding : FourVertex → FreeVertex :=
  Fin.castLE (by omega : 4 ≤ 14)

theorem fourEmbedding_injective : Function.Injective fourEmbedding :=
  Fin.castLE_injective (by omega : 4 ≤ 14)

structure FourExtension (kind : Kind) where
  tail : TailWitness kind
  inside : EdgeColoring FourVertex (Fin 4)
  rows : FourVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

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

def fourExtensionOfStar (w : CanonicalStarWitness ProfileC) :
    FourExtension (kindOfWitness w) :=
  restrictFour (extensionOfStar w)

def UniversalFourRowObstruction : Prop :=
  ∀ kind : Kind, ¬Nonempty (FourExtension kind)

theorem no_profileC_star_of_universalFourRowObstruction
    (h : UniversalFourRowObstruction) :
    ¬Nonempty (CanonicalStarWitness ProfileC) := by
  rintro ⟨w⟩
  exact h (kindOfWitness w) ⟨fourExtensionOfStar w⟩

#print axioms R4333.ProfileCFourRowBoundary.restrictFour
#print axioms R4333.ProfileCFourRowBoundary.no_profileC_star_of_universalFourRowObstruction

end ProfileCFourRowBoundary

end R4333
