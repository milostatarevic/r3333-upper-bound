import R4333Lean.ProfileBCFourRowBoundary

/-!
# Three-row threshold boundary for profile B

The profile-B structured tail has 47 vertices.  Three vertices from the
omitted block, together with that tail and the distinguished root, make 51
vertices.  Thus three rows are the smallest restriction aligned with the
open `K51` threshold: two rows would reconstruct only a `K50`, which may be
triangle-free in four colours.

Every full profile-B extension restricts to this exact object.  A universal
three-row obstruction therefore eliminates the whole profile-B branch.  It
also implies the older four-row fallback by restriction.
-/

namespace R4333
namespace ProfileBThreeRowBoundary

open SingleRootStarCNF
open ProfileBRowExtension
open ColoringJoinRows

abbrev ThreeVertex := Fin 3

def threeEmbedding : ThreeVertex → FreeVertex :=
  Fin.castLE (by omega : 3 ≤ 13)

theorem threeEmbedding_injective : Function.Injective threeEmbedding :=
  Fin.castLE_injective (by omega : 3 ≤ 13)

structure ThreeExtension (kind : Kind) where
  tail : TailWitness kind
  inside : EdgeColoring ThreeVertex (Fin 4)
  rows : ThreeVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

def restrictThree {kind : Kind} (ext : Extension kind) :
    ThreeExtension kind where
  tail := ext.tail
  inside := pullbackColoring ext.inside threeEmbedding
  rows := fun a ↦ ext.rows (threeEmbedding a)
  insideNoMono :=
    noMono_pullback ext.inside threeEmbedding threeEmbedding_injective
      ext.insideNoMono
  insideRootForbidden := by
    intro a b hab
    apply ext.insideRootForbidden (threeEmbedding a) (threeEmbedding b)
    exact fun h ↦ hab (threeEmbedding_injective h)
  rowsAdmissible := fun a ↦ ext.rowsAdmissible (threeEmbedding a)
  rowsPairCompatible := by
    intro a b hab x
    apply ext.rowsPairCompatible (threeEmbedding a) (threeEmbedding b)
    exact fun h ↦ hab (threeEmbedding_injective h)

def threeExtensionOfStar (w : CanonicalStarWitness ProfileB) :
    ThreeExtension (kindOfWitness w) :=
  restrictThree (extensionOfStar w)

def UniversalThreeRowObstruction : Prop :=
  ∀ kind : Kind, ¬Nonempty (ThreeExtension kind)

theorem no_profileB_star_of_universalThreeRowObstruction
    (h : UniversalThreeRowObstruction) :
    ¬Nonempty (CanonicalStarWitness ProfileB) := by
  rintro ⟨w⟩
  exact h (kindOfWitness w) ⟨threeExtensionOfStar w⟩

def threeOfFour {kind : Kind}
    (ext : ProfileBFourRowBoundary.FourExtension kind) :
    ThreeExtension kind := by
  let embedding : ThreeVertex → ProfileBFourRowBoundary.FourVertex :=
    Fin.castLE (by omega : 3 ≤ 4)
  have hinjective : Function.Injective embedding :=
    Fin.castLE_injective (by omega : 3 ≤ 4)
  exact {
    tail := ext.tail
    inside := pullbackColoring ext.inside embedding
    rows := fun a ↦ ext.rows (embedding a)
    insideNoMono :=
      noMono_pullback ext.inside embedding hinjective ext.insideNoMono
    insideRootForbidden := by
      intro a b hab
      apply ext.insideRootForbidden (embedding a) (embedding b)
      exact fun h ↦ hab (hinjective h)
    rowsAdmissible := fun a ↦ ext.rowsAdmissible (embedding a)
    rowsPairCompatible := by
      intro a b hab x
      apply ext.rowsPairCompatible (embedding a) (embedding b)
      exact fun h ↦ hab (hinjective h)
  }

theorem universalFourRowObstruction_of_universalThreeRowObstruction
    (h : UniversalThreeRowObstruction) :
    ProfileBFourRowBoundary.UniversalFourRowObstruction := by
  intro kind
  rintro ⟨ext⟩
  exact h kind ⟨threeOfFour ext⟩

#print axioms R4333.ProfileBThreeRowBoundary.restrictThree
#print axioms R4333.ProfileBThreeRowBoundary.no_profileB_star_of_universalThreeRowObstruction
#print axioms R4333.ProfileBThreeRowBoundary.universalFourRowObstruction_of_universalThreeRowObstruction

end ProfileBThreeRowBoundary
end R4333
