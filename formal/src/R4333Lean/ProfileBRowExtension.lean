import R4333Lean.ColoringJoinRows
import R4333Lean.SingleRootStarWitness61

/-!
# Exact row-extension data forced by a profile-B star

Every canonical `(13,15,16,16)` star splits into its first thirteen
vertices and the remaining `K15 + K16 + K16` tail.  This file retains all
semantic data inherited by that tail: triangle-freeness, the root-forbidden
colour in each of its three blocks, and the exact selected critical
template in each block.  It then records the thirteen individually
admissible, pair-compatible rows from the first block into that exact tail.

The final theorem is only a conditional elimination interface.  No
nonexistence assertion or finite-search result is made here.
-/

namespace R4333
namespace ProfileBRowExtension

open SingleRootStarCNF
open ColoringJoinRows

abbrev ProfileB := SingleRootStarCNF.Profile.p13_15_16_16
abbrev FreeVertex := Fin 13
abbrev TailVertex := Fin 47

/-! ## The exact tail type -/

/-- The eight choices of the K15, first K16, and second K16 template bits. -/
inductive Kind where
  | uuu | uut | utu | utt | tuu | tut | ttu | ttt
  deriving DecidableEq, Fintype, Repr

/-- `false` denotes the untwisted template and `true` the twisted one. -/
def Kind.twisted : Kind → Fin 3 → Bool
  | .uuu => ![false, false, false]
  | .uut => ![false, false, true]
  | .utu => ![false, true, false]
  | .utt => ![false, true, true]
  | .tuu => ![true, false, false]
  | .tut => ![true, false, true]
  | .ttu => ![true, true, false]
  | .ttt => ![true, true, true]

def Kind.ofBooleans : Bool → Bool → Bool → Kind
  | false, false, false => .uuu
  | false, false, true => .uut
  | false, true, false => .utu
  | false, true, true => .utt
  | true, false, false => .tuu
  | true, false, true => .tut
  | true, true, false => .ttu
  | true, true, true => .ttt

@[simp] theorem Kind.twisted_ofBooleans
    (first second third : Bool) (block : Fin 3) :
    (Kind.ofBooleans first second third).twisted block =
      ![first, second, third] block := by
  cases first <;> cases second <;> cases third <;> fin_cases block <;> rfl

/-- Local orders of the three tail blocks. -/
def blockSize : Fin 3 → Nat := ![15, 16, 16]

/-- Consecutive local starts inside `Fin 47`. -/
def blockStart : Fin 3 → Nat := ![0, 15, 31]

theorem blockStart_add_lt_fortySeven (block : Fin 3) {position : Nat}
    (hposition : position < blockSize block) :
    blockStart block + position < 47 := by
  fin_cases block <;> simp [blockSize, blockStart] at hposition ⊢ <;> omega

def blockVertex (block : Fin 3) (position : Nat) : TailVertex :=
  ⟨(blockStart block + position) % 47, Nat.mod_lt _ (by decide)⟩

@[simp] theorem blockVertex_val (block : Fin 3) {position : Nat}
    (hposition : position < blockSize block) :
    (blockVertex block position).val = blockStart block + position := by
  simp [blockVertex,
    Nat.mod_eq_of_lt (blockStart_add_lt_fortySeven block hposition)]

/-- Add the omitted first-block offset.  The image is labels `13,...,59`. -/
def tailEmbedding (x : TailVertex) : Fin 60 := ⟨13 + x.val, by omega⟩

theorem tailEmbedding_injective : Function.Injective tailEmbedding := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp only [tailEmbedding] at hval
  omega

@[simp] theorem star_blockSize_tail (block : Fin 3) :
    SingleRootStarCNF.blockSize ProfileB (Fin.succ block) = blockSize block := by
  fin_cases block <;> decide

@[simp] theorem star_blockStart_tail (block : Fin 3) :
    SingleRootStarCNF.blockStart ProfileB (Fin.succ block) =
      13 + blockStart block := by
  fin_cases block <;> decide

theorem tailEmbedding_blockVertex (block : Fin 3) (position : Nat)
    (hposition : position < blockSize block) :
    tailEmbedding (blockVertex block position) =
      SingleRootStarCNF.blockVertex ProfileB (Fin.succ block) position := by
  apply Fin.ext
  have hstar :
      position < SingleRootStarCNF.blockSize ProfileB (Fin.succ block) := by
    rw [star_blockSize_tail]
    exact hposition
  rw [SingleRootStarCNF.blockVertex_val ProfileB (Fin.succ block) hstar,
    star_blockStart_tail]
  simp [tailEmbedding, blockVertex_val block hposition]
  omega

/-- The exact semantic `K15 + K16 + K16` tail inherited from profile B.
The root-forbidden field is retained explicitly even though it also follows
from the displayed canonical palettes for these three critical blocks. -/
structure TailWitness (kind : Kind) where
  coloring : EdgeColoring TailVertex (Fin 4)
  noMono : NoMonochromaticTriangle coloring
  rootForbidden : ∀ (block : Fin 3) (left right : Nat),
    left < blockSize block → right < blockSize block → left < right →
    coloring (blockVertex block left) (blockVertex block right) ≠
      Fin.succ block
  templateCanonical : ∀ (block : Fin 3),
    isCriticalBlock ProfileB (Fin.succ block) →
    ∀ (left right : Nat),
      left < blockSize block → right < blockSize block → left < right →
      coloring (blockVertex block left) (blockVertex block right) =
        canonicalPalette (Fin.succ block)
          (templateColor (blockSize block) (kind.twisted block) left right)

def tailColoring (w : CanonicalStarWitness ProfileB) :
    EdgeColoring TailVertex (Fin 4) :=
  pullbackColoring w.coloring tailEmbedding

theorem tailColoring_noMono (w : CanonicalStarWitness ProfileB) :
    NoMonochromaticTriangle (tailColoring w) :=
  noMono_pullback w.coloring tailEmbedding tailEmbedding_injective w.noMono

def kindOfWitness (w : CanonicalStarWitness ProfileB) : Kind :=
  Kind.ofBooleans (w.chosenTemplate 1) (w.chosenTemplate 2)
    (w.chosenTemplate 3)

@[simp] theorem kindOfWitness_twisted
    (w : CanonicalStarWitness ProfileB) (block : Fin 3) :
    (kindOfWitness w).twisted block = w.chosenTemplate (Fin.succ block) := by
  rw [kindOfWitness, Kind.twisted_ofBooleans]
  fin_cases block <;> rfl

/-- Restrict a full profile-B star to the exact remaining tail. -/
def tailWitnessOfStar (w : CanonicalStarWitness ProfileB) :
    TailWitness (kindOfWitness w) where
  coloring := tailColoring w
  noMono := tailColoring_noMono w
  rootForbidden := by
    intro block left right hleft hright hlr
    have hleftStar :
        left < SingleRootStarCNF.blockSize ProfileB (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hleft
    have hrightStar :
        right < SingleRootStarCNF.blockSize ProfileB (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hright
    have hforbidden := w.rootForbidden (Fin.succ block) left right
      hleftStar hrightStar hlr
    change w.coloring (tailEmbedding (blockVertex block left))
        (tailEmbedding (blockVertex block right)) ≠ _
    rw [tailEmbedding_blockVertex block left hleft,
      tailEmbedding_blockVertex block right hright]
    exact hforbidden
  templateCanonical := by
    intro block hcritical left right hleft hright hlr
    have hleftStar :
        left < SingleRootStarCNF.blockSize ProfileB (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hleft
    have hrightStar :
        right < SingleRootStarCNF.blockSize ProfileB (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hright
    have htemplate := w.templateCanonical (Fin.succ block) hcritical
      left right hleftStar hrightStar hlr
    change w.coloring (tailEmbedding (blockVertex block left))
        (tailEmbedding (blockVertex block right)) = _
    rw [tailEmbedding_blockVertex block left hleft,
      tailEmbedding_blockVertex block right hright]
    rw [star_blockSize_tail] at htemplate
    simpa using htemplate

/-! ## Exact join and row decomposition -/

def freeEmbedding (x : FreeVertex) : Fin 60 := ⟨x.val, by omega⟩

theorem freeEmbedding_injective : Function.Injective freeEmbedding := by
  intro x y h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa [freeEmbedding] using hval

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

def insideColoring (w : CanonicalStarWitness ProfileB) :
    EdgeColoring FreeVertex (Fin 4) :=
  pullbackColoring w.coloring freeEmbedding

def crossRows (w : CanonicalStarWitness ProfileB) :
    FreeVertex → TailVertex → Fin 4 := fun a x ↦
  w.coloring (freeEmbedding a) (tailEmbedding x)

theorem joinedColoring_eq_pullback (w : CanonicalStarWitness ProfileB) :
    joinColoring (insideColoring w) (tailColoring w) (crossRows w) =
      pullbackColoring w.coloring splitToFin := by
  ext u v
  cases u <;> cases v <;>
    simp [joinColoring, insideColoring, tailColoring, crossRows,
      pullbackColoring, splitToFin, w.coloring.color_symm]

theorem joinedColoring_noMono (w : CanonicalStarWitness ProfileB) :
    NoMonochromaticTriangle
      (joinColoring (insideColoring w) (tailColoring w) (crossRows w)) := by
  rw [joinedColoring_eq_pullback]
  exact noMono_pullback w.coloring splitToFin splitToFin_injective w.noMono

theorem star_blockVertex_zero_eq_freeEmbedding
    (position : Nat) (hposition : position < 13) :
    SingleRootStarCNF.blockVertex ProfileB 0 position =
      (⟨position, Nat.lt_trans hposition (by decide : 13 < 60)⟩ : Fin 60) := by
  apply Fin.ext
  simp [SingleRootStarCNF.blockVertex, SingleRootStarCNF.blockStart,
    profileSizes, Nat.mod_eq_of_lt
      (Nat.lt_trans hposition (by decide : 13 < 60))]

theorem insideColoring_rootForbidden (w : CanonicalStarWitness ProfileB) :
    ∀ a b : FreeVertex, a ≠ b → insideColoring w a b ≠ 0 := by
  intro a b hab
  have hval : a.val ≠ b.val := fun h ↦ hab (Fin.ext h)
  change w.coloring (freeEmbedding a) (freeEmbedding b) ≠ 0
  have haVertex :
      SingleRootStarCNF.blockVertex ProfileB 0 a.val = freeEmbedding a := by
    apply Fin.ext
    simp [star_blockVertex_zero_eq_freeEmbedding, freeEmbedding]
  have hbVertex :
      SingleRootStarCNF.blockVertex ProfileB 0 b.val = freeEmbedding b := by
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

/-- Exact reduced row-extension object forced by a full profile-B star. -/
structure Extension (kind : Kind) where
  tail : TailWitness kind
  inside : EdgeColoring FreeVertex (Fin 4)
  rows : FreeVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

def extensionOfStar (w : CanonicalStarWitness ProfileB) :
    Extension (kindOfWitness w) := by
  have hdecomp :=
    (noMono_joinColoring_iff
      (insideColoring w) (tailColoring w) (crossRows w)).mp
        (joinedColoring_noMono w)
  exact {
    tail := tailWitnessOfStar w
    inside := insideColoring w
    rows := crossRows w
    insideNoMono := hdecomp.1
    insideRootForbidden := insideColoring_rootForbidden w
    rowsAdmissible := hdecomp.2.2.1
    rowsPairCompatible := hdecomp.2.2.2
  }

theorem exists_rowExtension_of_star
    (w : CanonicalStarWitness ProfileB) :
    ∃ kind : Kind, Nonempty (Extension kind) :=
  ⟨kindOfWitness w, ⟨extensionOfStar w⟩⟩

/-- Universal elimination of the exact row objects eliminates profile B. -/
theorem no_profileB_star_of_no_rowExtensions
    (h : ∀ kind : Kind, ¬Nonempty (Extension kind)) :
    ¬Nonempty (CanonicalStarWitness ProfileB) := by
  rintro ⟨w⟩
  obtain ⟨kind, hext⟩ := exists_rowExtension_of_star w
  exact h kind hext

#print axioms R4333.ProfileBRowExtension.tailWitnessOfStar
#print axioms R4333.ProfileBRowExtension.joinedColoring_noMono
#print axioms R4333.ProfileBRowExtension.insideColoring_rootForbidden
#print axioms R4333.ProfileBRowExtension.extensionOfStar
#print axioms R4333.ProfileBRowExtension.no_profileB_star_of_no_rowExtensions

end ProfileBRowExtension
end R4333
