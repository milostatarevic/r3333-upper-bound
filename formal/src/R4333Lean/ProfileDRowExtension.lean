import R4333Lean.ColoringJoinRows
import R4333Lean.ProfileDTripleJoinReduction

/-!
# Exact row-extension data forced by a profile-D star

This file connects the abstract row semantics to the canonical
`(14,15,15,16)` star.  Every full profile-D witness yields:

* one exact three-block tail witness;
* a triangle-free colouring on the omitted fourteen vertices, with colour
  zero forbidden internally; and
* fourteen individually admissible tail rows whose pairwise available
  colours contain their internal edge colours.

This is a necessary semantic reduction, not an assumption and not a finite
search claim.
-/

namespace R4333
namespace ProfileDRowExtension

open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ColoringJoinRows

abbrev FreeVertex := Fin 14
abbrev TailVertex := Fin 46

def freeEmbedding (x : FreeVertex) : Fin 60 := ⟨x.val, by omega⟩

theorem freeEmbedding_injective : Function.Injective freeEmbedding := by
  intro x y h
  apply Fin.ext
  have hval : (freeEmbedding x).val = (freeEmbedding y).val :=
    congrArg Fin.val h
  simpa [freeEmbedding] using hval

/-- The canonical sum decomposition of the sixty non-root vertices. -/
def splitToFin : Sum FreeVertex TailVertex → Fin 60
  | .inl x => freeEmbedding x
  | .inr y => tailEmbedding y

theorem splitToFin_injective : Function.Injective splitToFin := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have h := freeEmbedding_injective hxy
          subst y
          rfl
      | inr y =>
          exfalso
          have hval := congrArg Fin.val hxy
          simp [splitToFin, freeEmbedding, tailEmbedding] at hval
          omega
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          have hval := congrArg Fin.val hxy
          simp [splitToFin, freeEmbedding, tailEmbedding] at hval
          omega
      | inr y =>
          have h := tailEmbedding_injective hxy
          subst y
          rfl

def insideColoring (w : CanonicalStarWitness ProfileD) :
    EdgeColoring FreeVertex (Fin 4) :=
  pullbackColoring w.coloring freeEmbedding

def crossRows (w : CanonicalStarWitness ProfileD) :
    FreeVertex → TailVertex → Fin 4 := fun a x ↦
  w.coloring (freeEmbedding a) (tailEmbedding x)

theorem joinedColoring_eq_pullback (w : CanonicalStarWitness ProfileD) :
    joinColoring (insideColoring w) (tailColoring w) (crossRows w) =
      pullbackColoring w.coloring splitToFin := by
  ext u v
  cases u <;> cases v <;>
    simp [joinColoring, insideColoring, tailColoring, crossRows,
      pullbackColoring, splitToFin, w.coloring.color_symm]

theorem joinedColoring_noMono (w : CanonicalStarWitness ProfileD) :
    NoMonochromaticTriangle
      (joinColoring (insideColoring w) (tailColoring w) (crossRows w)) := by
  rw [joinedColoring_eq_pullback]
  exact noMono_pullback w.coloring splitToFin splitToFin_injective w.noMono

theorem star_blockVertex_zero_eq_freeEmbedding
    (position : Nat) (hposition : position < 14) :
    SingleRootStarCNF.blockVertex ProfileD 0 position =
      (⟨position, Nat.lt_trans hposition (by decide : 14 < 60)⟩ : Fin 60) := by
  apply Fin.ext
  simp [SingleRootStarCNF.blockVertex, SingleRootStarCNF.blockStart,
    profileSizes, Nat.mod_eq_of_lt
      (Nat.lt_trans hposition (by decide : 14 < 60))]

theorem insideColoring_rootForbidden (w : CanonicalStarWitness ProfileD) :
    ∀ a b : FreeVertex, a ≠ b → insideColoring w a b ≠ 0 := by
  intro a b hab
  have hval : a.val ≠ b.val := fun h ↦ hab (Fin.ext h)
  change w.coloring (freeEmbedding a) (freeEmbedding b) ≠ 0
  have haVertex :
      SingleRootStarCNF.blockVertex ProfileD 0 a.val = freeEmbedding a := by
    apply Fin.ext
    simp [star_blockVertex_zero_eq_freeEmbedding, freeEmbedding]
  have hbVertex :
      SingleRootStarCNF.blockVertex ProfileD 0 b.val = freeEmbedding b := by
    apply Fin.ext
    simp [star_blockVertex_zero_eq_freeEmbedding, freeEmbedding]
  rw [← haVertex, ← hbVertex]
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact w.rootForbidden 0 a.val b.val
      (by simp [SingleRootStarCNF.blockSize, profileSizes])
      (by simp [SingleRootStarCNF.blockSize, profileSizes]) hlt
  · intro hedge
    apply w.rootForbidden 0 b.val a.val
      (by simp [SingleRootStarCNF.blockSize, profileSizes])
      (by simp [SingleRootStarCNF.blockSize, profileSizes]) hgt
    rw [w.coloring.color_symm]
    exact hedge

/-- Exact reduced extension object forced by a full profile-D star. -/
structure Extension (kind : Kind) where
  tail : Witness kind
  inside : EdgeColoring FreeVertex (Fin 4)
  rows : FreeVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

/-- Restrict a full canonical star to its exact row-extension data. -/
def extensionOfStar (w : CanonicalStarWitness ProfileD) :
    Extension (kindOfWitness w) := by
  have hdecomp :=
    (noMono_joinColoring_iff
      (insideColoring w) (tailColoring w) (crossRows w)).mp
        (joinedColoring_noMono w)
  exact {
    tail := witnessOfStar w
    inside := insideColoring w
    rows := crossRows w
    insideNoMono := hdecomp.1
    insideRootForbidden := insideColoring_rootForbidden w
    rowsAdmissible := hdecomp.2.2.1
    rowsPairCompatible := hdecomp.2.2.2
  }

theorem exists_rowExtension_of_star
    (w : CanonicalStarWitness ProfileD) :
    ∃ kind : Kind, Nonempty (Extension kind) :=
  ⟨kindOfWitness w, ⟨extensionOfStar w⟩⟩

/-- Any universal obstruction to the exact reduced row-extension objects
eliminates the full profile-D branch. -/
theorem no_profileD_star_of_no_rowExtensions
    (h : ∀ kind : Kind, ¬Nonempty (Extension kind)) :
    ¬Nonempty (CanonicalStarWitness ProfileD) := by
  rintro ⟨w⟩
  obtain ⟨kind, hext⟩ := exists_rowExtension_of_star w
  exact h kind hext

#print axioms R4333.ProfileDRowExtension.joinedColoring_noMono
#print axioms R4333.ProfileDRowExtension.insideColoring_rootForbidden
#print axioms R4333.ProfileDRowExtension.extensionOfStar
#print axioms R4333.ProfileDRowExtension.no_profileD_star_of_no_rowExtensions

end ProfileDRowExtension
end R4333
