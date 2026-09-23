import R4333Lean.ColoringJoinRows
import R4333Lean.SingleRootStarWitness61

/-!
# Exact row-extension data forced by a profile-C star

Every canonical `(14,14,16,16)` star splits into its first fourteen
vertices and the remaining `K14 + K16 + K16` tail.  The first tail block is
not critical, so it has no template selector; its inherited root-forbidden
colour-one law is therefore retained explicitly.  The two K16 blocks keep
their exact selected canonical templates as well as their root-forbidden
laws.  Fourteen admissible, pair-compatible rows attach the omitted first
block to this exact tail.

The endpoint is a conditional semantic elimination theorem only.
-/

namespace R4333
namespace ProfileCRowExtension

open SingleRootStarCNF
open ColoringJoinRows

abbrev ProfileC := SingleRootStarCNF.Profile.p14_14_16_16
abbrev FreeVertex := Fin 14
abbrev TailVertex := Fin 46

/-! ## The exact tail type -/

/-- The four choices of the two K16 template bits. -/
inductive Kind where
  | uu | ut | tu | tt
  deriving DecidableEq, Fintype, Repr

/-- Local block zero is the noncritical K14 and has no selector.  Its
displayed `false` value is never used by `TailWitness.templateCanonical`;
the two remaining entries are the genuine K16 selectors. -/
def Kind.twisted : Kind → Fin 3 → Bool
  | .uu => ![false, false, false]
  | .ut => ![false, false, true]
  | .tu => ![false, true, false]
  | .tt => ![false, true, true]

def Kind.ofBooleans : Bool → Bool → Kind
  | false, false => .uu
  | false, true => .ut
  | true, false => .tu
  | true, true => .tt

@[simp] theorem Kind.twisted_ofBooleans_zero
    (first second : Bool) :
    (Kind.ofBooleans first second).twisted 0 = false := by
  cases first <;> cases second <;> rfl

@[simp] theorem Kind.twisted_ofBooleans_one
    (first second : Bool) :
    (Kind.ofBooleans first second).twisted 1 = first := by
  cases first <;> cases second <;> rfl

@[simp] theorem Kind.twisted_ofBooleans_two
    (first second : Bool) :
    (Kind.ofBooleans first second).twisted 2 = second := by
  cases first <;> cases second <;> rfl

/-- Local orders of the three tail blocks. -/
def blockSize : Fin 3 → Nat := ![14, 16, 16]

/-- Consecutive local starts inside `Fin 46`. -/
def blockStart : Fin 3 → Nat := ![0, 14, 30]

theorem blockStart_add_lt_fortySix (block : Fin 3) {position : Nat}
    (hposition : position < blockSize block) :
    blockStart block + position < 46 := by
  fin_cases block <;> simp [blockSize, blockStart] at hposition ⊢ <;> omega

def blockVertex (block : Fin 3) (position : Nat) : TailVertex :=
  ⟨(blockStart block + position) % 46, Nat.mod_lt _ (by decide)⟩

@[simp] theorem blockVertex_val (block : Fin 3) {position : Nat}
    (hposition : position < blockSize block) :
    (blockVertex block position).val = blockStart block + position := by
  simp [blockVertex,
    Nat.mod_eq_of_lt (blockStart_add_lt_fortySix block hposition)]

/-- Add the omitted first-block offset.  The image is labels `14,...,59`. -/
def tailEmbedding (x : TailVertex) : Fin 60 := ⟨14 + x.val, by omega⟩

theorem tailEmbedding_injective : Function.Injective tailEmbedding := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp only [tailEmbedding] at hval
  omega

@[simp] theorem star_blockSize_tail (block : Fin 3) :
    SingleRootStarCNF.blockSize ProfileC (Fin.succ block) = blockSize block := by
  fin_cases block <;> decide

@[simp] theorem star_blockStart_tail (block : Fin 3) :
    SingleRootStarCNF.blockStart ProfileC (Fin.succ block) =
      14 + blockStart block := by
  fin_cases block <;> decide

theorem tailEmbedding_blockVertex (block : Fin 3) (position : Nat)
    (hposition : position < blockSize block) :
    tailEmbedding (blockVertex block position) =
      SingleRootStarCNF.blockVertex ProfileC (Fin.succ block) position := by
  apply Fin.ext
  have hstar :
      position < SingleRootStarCNF.blockSize ProfileC (Fin.succ block) := by
    rw [star_blockSize_tail]
    exact hposition
  rw [SingleRootStarCNF.blockVertex_val ProfileC (Fin.succ block) hstar,
    star_blockStart_tail]
  simp [tailEmbedding, blockVertex_val block hposition]
  omega

/-- The exact semantic `K14 + K16 + K16` tail inherited from profile C.
In particular, `rootForbidden` is essential for the noncritical K14 block;
it is not silently replaced by a template assertion. -/
structure TailWitness (kind : Kind) where
  coloring : EdgeColoring TailVertex (Fin 4)
  noMono : NoMonochromaticTriangle coloring
  rootForbidden : ∀ (block : Fin 3) (left right : Nat),
    left < blockSize block → right < blockSize block → left < right →
    coloring (blockVertex block left) (blockVertex block right) ≠
      Fin.succ block
  templateCanonical : ∀ (block : Fin 3),
    isCriticalBlock ProfileC (Fin.succ block) →
    ∀ (left right : Nat),
      left < blockSize block → right < blockSize block → left < right →
      coloring (blockVertex block left) (blockVertex block right) =
        canonicalPalette (Fin.succ block)
          (templateColor (blockSize block) (kind.twisted block) left right)

def tailColoring (w : CanonicalStarWitness ProfileC) :
    EdgeColoring TailVertex (Fin 4) :=
  pullbackColoring w.coloring tailEmbedding

theorem tailColoring_noMono (w : CanonicalStarWitness ProfileC) :
    NoMonochromaticTriangle (tailColoring w) :=
  noMono_pullback w.coloring tailEmbedding tailEmbedding_injective w.noMono

def kindOfWitness (w : CanonicalStarWitness ProfileC) : Kind :=
  Kind.ofBooleans (w.chosenTemplate 2) (w.chosenTemplate 3)

theorem kindOfWitness_twisted_of_critical
    (w : CanonicalStarWitness ProfileC) (block : Fin 3)
    (hcritical : isCriticalBlock ProfileC (Fin.succ block)) :
    (kindOfWitness w).twisted block = w.chosenTemplate (Fin.succ block) := by
  fin_cases block
  · simp [isCriticalBlock, SingleRootStarCNF.blockSize, profileSizes]
      at hcritical
  · simp [kindOfWitness]
  · simp [kindOfWitness]

/-- Restrict a full profile-C star to the exact remaining tail. -/
def tailWitnessOfStar (w : CanonicalStarWitness ProfileC) :
    TailWitness (kindOfWitness w) where
  coloring := tailColoring w
  noMono := tailColoring_noMono w
  rootForbidden := by
    intro block left right hleft hright hlr
    have hleftStar :
        left < SingleRootStarCNF.blockSize ProfileC (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hleft
    have hrightStar :
        right < SingleRootStarCNF.blockSize ProfileC (Fin.succ block) := by
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
        left < SingleRootStarCNF.blockSize ProfileC (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hleft
    have hrightStar :
        right < SingleRootStarCNF.blockSize ProfileC (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hright
    have htemplate := w.templateCanonical (Fin.succ block) hcritical
      left right hleftStar hrightStar hlr
    change w.coloring (tailEmbedding (blockVertex block left))
        (tailEmbedding (blockVertex block right)) = _
    rw [tailEmbedding_blockVertex block left hleft,
      tailEmbedding_blockVertex block right hright]
    rw [star_blockSize_tail] at htemplate
    simpa [kindOfWitness_twisted_of_critical w block hcritical]
      using htemplate

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

def insideColoring (w : CanonicalStarWitness ProfileC) :
    EdgeColoring FreeVertex (Fin 4) :=
  pullbackColoring w.coloring freeEmbedding

def crossRows (w : CanonicalStarWitness ProfileC) :
    FreeVertex → TailVertex → Fin 4 := fun a x ↦
  w.coloring (freeEmbedding a) (tailEmbedding x)

theorem joinedColoring_eq_pullback (w : CanonicalStarWitness ProfileC) :
    joinColoring (insideColoring w) (tailColoring w) (crossRows w) =
      pullbackColoring w.coloring splitToFin := by
  ext u v
  cases u <;> cases v <;>
    simp [joinColoring, insideColoring, tailColoring, crossRows,
      pullbackColoring, splitToFin, w.coloring.color_symm]

theorem joinedColoring_noMono (w : CanonicalStarWitness ProfileC) :
    NoMonochromaticTriangle
      (joinColoring (insideColoring w) (tailColoring w) (crossRows w)) := by
  rw [joinedColoring_eq_pullback]
  exact noMono_pullback w.coloring splitToFin splitToFin_injective w.noMono

theorem star_blockVertex_zero_eq_freeEmbedding
    (position : Nat) (hposition : position < 14) :
    SingleRootStarCNF.blockVertex ProfileC 0 position =
      (⟨position, Nat.lt_trans hposition (by decide : 14 < 60)⟩ : Fin 60) := by
  apply Fin.ext
  simp [SingleRootStarCNF.blockVertex, SingleRootStarCNF.blockStart,
    profileSizes, Nat.mod_eq_of_lt
      (Nat.lt_trans hposition (by decide : 14 < 60))]

theorem insideColoring_rootForbidden (w : CanonicalStarWitness ProfileC) :
    ∀ a b : FreeVertex, a ≠ b → insideColoring w a b ≠ 0 := by
  intro a b hab
  have hval : a.val ≠ b.val := fun h ↦ hab (Fin.ext h)
  change w.coloring (freeEmbedding a) (freeEmbedding b) ≠ 0
  have haVertex :
      SingleRootStarCNF.blockVertex ProfileC 0 a.val = freeEmbedding a := by
    apply Fin.ext
    simp [star_blockVertex_zero_eq_freeEmbedding, freeEmbedding]
  have hbVertex :
      SingleRootStarCNF.blockVertex ProfileC 0 b.val = freeEmbedding b := by
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

/-- Exact reduced row-extension object forced by a full profile-C star. -/
structure Extension (kind : Kind) where
  tail : TailWitness kind
  inside : EdgeColoring FreeVertex (Fin 4)
  rows : FreeVertex → TailVertex → Fin 4
  insideNoMono : NoMonochromaticTriangle inside
  insideRootForbidden : ∀ a b, a ≠ b → inside a b ≠ 0
  rowsAdmissible : ∀ a, RowAdmissible tail.coloring (rows a)
  rowsPairCompatible : RowPairCompatible inside rows

def extensionOfStar (w : CanonicalStarWitness ProfileC) :
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
    (w : CanonicalStarWitness ProfileC) :
    ∃ kind : Kind, Nonempty (Extension kind) :=
  ⟨kindOfWitness w, ⟨extensionOfStar w⟩⟩

/-- Universal elimination of the exact row objects eliminates profile C. -/
theorem no_profileC_star_of_no_rowExtensions
    (h : ∀ kind : Kind, ¬Nonempty (Extension kind)) :
    ¬Nonempty (CanonicalStarWitness ProfileC) := by
  rintro ⟨w⟩
  obtain ⟨kind, hext⟩ := exists_rowExtension_of_star w
  exact h kind hext

#print axioms R4333.ProfileCRowExtension.kindOfWitness_twisted_of_critical
#print axioms R4333.ProfileCRowExtension.tailWitnessOfStar
#print axioms R4333.ProfileCRowExtension.joinedColoring_noMono
#print axioms R4333.ProfileCRowExtension.insideColoring_rootForbidden
#print axioms R4333.ProfileCRowExtension.extensionOfStar
#print axioms R4333.ProfileCRowExtension.no_profileC_star_of_no_rowExtensions

end ProfileCRowExtension
end R4333
