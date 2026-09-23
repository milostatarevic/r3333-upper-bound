import R4333Lean.ProfileCFourRowKindSymmetry
import R4333Lean.ProfileDFourRowKindSymmetry

/-!
# Free-vertex symmetry of the four-row boundaries

The four free vertices in the profile-C and profile-D boundary objects are
labels only.  Every permutation of `Fin 4` therefore acts by pulling back the
inside colouring and reindexing the four tail rows.  This action leaves the
tail kind and every host colour unchanged.
-/

namespace R4333

namespace ProfileCFourRowFreeVertexSymmetry

open ColoringJoinRows
open ProfileCRowExtension
open ProfileCFourRowBoundary

/-- Relabel the four free vertices of a profile-C boundary object. -/
def transportFourExtension {kind : Kind}
    (σ : Equiv.Perm FourVertex) (ext : FourExtension kind) :
    FourExtension kind where
  tail := ext.tail
  inside := pullbackColoring ext.inside σ
  rows := fun a => ext.rows (σ a)
  insideNoMono :=
    noMono_pullback ext.inside σ σ.injective ext.insideNoMono
  insideRootForbidden := by
    intro a b hab
    exact ext.insideRootForbidden (σ a) (σ b)
      (fun h => hab (σ.injective h))
  rowsAdmissible := fun a => ext.rowsAdmissible (σ a)
  rowsPairCompatible := by
    intro a b hab x hbad
    exact ext.rowsPairCompatible (σ a) (σ b)
      (fun h => hab (σ.injective h)) x hbad

@[simp] theorem transportFourExtension_inside {kind : Kind}
    (σ : Equiv.Perm FourVertex) (ext : FourExtension kind)
    (a b : FourVertex) :
    (transportFourExtension σ ext).inside a b = ext.inside (σ a) (σ b) :=
  rfl

@[simp] theorem transportFourExtension_rows {kind : Kind}
    (σ : Equiv.Perm FourVertex) (ext : FourExtension kind)
    (a : FourVertex) :
    (transportFourExtension σ ext).rows a = ext.rows (σ a) :=
  rfl

end ProfileCFourRowFreeVertexSymmetry

namespace ProfileDFourRowFreeVertexSymmetry

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary

/-- Relabel the four free vertices of a profile-D boundary object. -/
def transportFourExtension {kind : Kind}
    (σ : Equiv.Perm FourVertex) (ext : FourExtension kind) :
    FourExtension kind where
  tail := ext.tail
  inside := pullbackColoring ext.inside σ
  rows := fun a => ext.rows (σ a)
  insideNoMono :=
    noMono_pullback ext.inside σ σ.injective ext.insideNoMono
  insideRootForbidden := by
    intro a b hab
    exact ext.insideRootForbidden (σ a) (σ b)
      (fun h => hab (σ.injective h))
  rowsAdmissible := fun a => ext.rowsAdmissible (σ a)
  rowsPairCompatible := by
    intro a b hab x hbad
    exact ext.rowsPairCompatible (σ a) (σ b)
      (fun h => hab (σ.injective h)) x hbad

@[simp] theorem transportFourExtension_inside {kind : Kind}
    (σ : Equiv.Perm FourVertex) (ext : FourExtension kind)
    (a b : FourVertex) :
    (transportFourExtension σ ext).inside a b = ext.inside (σ a) (σ b) :=
  rfl

@[simp] theorem transportFourExtension_rows {kind : Kind}
    (σ : Equiv.Perm FourVertex) (ext : FourExtension kind)
    (a : FourVertex) :
    (transportFourExtension σ ext).rows a = ext.rows (σ a) :=
  rfl

end ProfileDFourRowFreeVertexSymmetry

#print axioms R4333.ProfileCFourRowFreeVertexSymmetry.transportFourExtension
#print axioms R4333.ProfileDFourRowFreeVertexSymmetry.transportFourExtension

end R4333
