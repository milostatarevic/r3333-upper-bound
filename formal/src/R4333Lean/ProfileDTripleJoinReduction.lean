import R4333Lean.SingleRootStarWitness61
import R4333Lean.Obstruction

/-!
# The exact K15 + K15 + K16 tail of profile D

The last three blocks of the canonical `(14,15,15,16)` single-root star form
one contiguous 46-vertex interval.  This file restricts a full star witness
to that interval and records the eight possible untwisted/twisted template
choices explicitly.

There is no finite-search conclusion here.  The endpoint says that eight
semantic refutations of these exact three-block joins would eliminate the
whole profile-D star branch.  In particular, the reduction does not use a
degree cap, sampled pair witness, or unverified catalogue claim.
-/

namespace R4333

open SingleRootStarCNF

namespace ProfileDTripleJoinReduction

abbrev ProfileD := SingleRootStarCNF.Profile.p14_15_15_16

/-- The eight fixed choices of the two K15 kinds and the K16 kind. -/
inductive Kind where
  | uuu | uut | utu | utt | tuu | tut | ttu | ttt
  deriving DecidableEq, Fintype, Repr

/-- `false` is untwisted and `true` is twisted, in the three tail blocks. -/
def Kind.twisted : Kind → Fin 3 → Bool
  | .uuu => ![false, false, false]
  | .uut => ![false, false, true]
  | .utu => ![false, true, false]
  | .utt => ![false, true, true]
  | .tuu => ![true, false, false]
  | .tut => ![true, false, true]
  | .ttu => ![true, true, false]
  | .ttt => ![true, true, true]

/-- Package three independently selected template bits as one of the eight
fixed kinds. -/
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
def blockSize : Fin 3 → Nat := ![15, 15, 16]

/-- Consecutive local starts inside `Fin 46`. -/
def blockStart : Fin 3 → Nat := ![0, 15, 30]

theorem blockStart_add_lt_fortySix (block : Fin 3) {position : Nat}
    (hposition : position < blockSize block) :
    blockStart block + position < 46 := by
  fin_cases block <;> simp [blockSize, blockStart] at hposition ⊢ <;> omega

/-- The local vertex with a defensive modulus, matching the canonical star
coordinate style.  Under the advertised block bound, the modulus vanishes. -/
def blockVertex (block : Fin 3) (position : Nat) : Fin 46 :=
  ⟨(blockStart block + position) % 46,
    Nat.mod_lt _ (by decide)⟩

@[simp] theorem blockVertex_val (block : Fin 3) {position : Nat}
    (hposition : position < blockSize block) :
    (blockVertex block position).val = blockStart block + position := by
  simp [blockVertex,
    Nat.mod_eq_of_lt (blockStart_add_lt_fortySix block hposition)]

/-- Add the omitted first-block offset.  The image is exactly labels
`14,...,59` of the canonical profile-D star. -/
def tailEmbedding (x : Fin 46) : Fin 60 :=
  ⟨14 + x.val, by omega⟩

theorem tailEmbedding_injective : Function.Injective tailEmbedding := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp only [tailEmbedding] at hval
  omega

@[simp] theorem star_blockSize_tail (block : Fin 3) :
    SingleRootStarCNF.blockSize ProfileD (Fin.succ block) = blockSize block := by
  fin_cases block <;> decide

@[simp] theorem star_blockStart_tail (block : Fin 3) :
    SingleRootStarCNF.blockStart ProfileD (Fin.succ block) =
      14 + blockStart block := by
  fin_cases block <;> decide

/-- Local and full-star labels agree definitionally after adding the tail
offset. -/
theorem tailEmbedding_blockVertex (block : Fin 3) (position : Nat)
    (hposition : position < blockSize block) :
    tailEmbedding (blockVertex block position) =
      SingleRootStarCNF.blockVertex ProfileD (Fin.succ block) position := by
  apply Fin.ext
  have hstar :
      position < SingleRootStarCNF.blockSize ProfileD (Fin.succ block) := by
    rw [star_blockSize_tail]
    exact hposition
  rw [SingleRootStarCNF.blockVertex_val ProfileD (Fin.succ block) hstar,
    star_blockStart_tail]
  simp [tailEmbedding, blockVertex_val block hposition]
  omega

/-- Exactly the triangle-free, canonically labelled three-block join that
remains after deleting the initial K14 block from profile D. -/
structure Witness (kind : Kind) where
  coloring : EdgeColoring (Fin 46) (Fin 4)
  noMono : NoMonochromaticTriangle coloring
  templateCanonical : ∀ (block : Fin 3) (left right : Nat),
    left < blockSize block →
    right < blockSize block → left < right →
    coloring (blockVertex block left) (blockVertex block right) =
      canonicalPalette (Fin.succ block)
        (templateColor (blockSize block) (kind.twisted block) left right)

/-- Restrict a full profile-D star colouring to the contiguous tail. -/
def tailColoring (w : CanonicalStarWitness ProfileD) :
    EdgeColoring (Fin 46) (Fin 4) :=
  pullbackColoring w.coloring tailEmbedding

theorem tailColoring_noMono (w : CanonicalStarWitness ProfileD) :
    NoMonochromaticTriangle (tailColoring w) :=
  noMono_pullback w.coloring tailEmbedding tailEmbedding_injective w.noMono

/-- The fixed kind selected by the three template selectors of a full
profile-D witness. -/
def kindOfWitness (w : CanonicalStarWitness ProfileD) : Kind :=
  Kind.ofBooleans (w.chosenTemplate 1) (w.chosenTemplate 2)
    (w.chosenTemplate 3)

@[simp] theorem kindOfWitness_twisted
    (w : CanonicalStarWitness ProfileD) (block : Fin 3) :
    (kindOfWitness w).twisted block = w.chosenTemplate (Fin.succ block) := by
  rw [kindOfWitness, Kind.twisted_ofBooleans]
  fin_cases block <;> rfl

theorem star_tail_block_critical (block : Fin 3) :
    isCriticalBlock ProfileD (Fin.succ block) := by
  fin_cases block <;> simp [isCriticalBlock, SingleRootStarCNF.blockSize,
    profileSizes]

/-- The exact semantic restriction of a full star witness. -/
def witnessOfStar (w : CanonicalStarWitness ProfileD) :
    Witness (kindOfWitness w) where
  coloring := tailColoring w
  noMono := tailColoring_noMono w
  templateCanonical := by
    intro block left right hleft hright hlr
    have hleftStar :
        left < SingleRootStarCNF.blockSize ProfileD (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hleft
    have hrightStar :
        right < SingleRootStarCNF.blockSize ProfileD (Fin.succ block) := by
      rw [star_blockSize_tail]
      exact hright
    have htemplate := w.templateCanonical (Fin.succ block)
      (star_tail_block_critical block) left right hleftStar hrightStar hlr
    change w.coloring (tailEmbedding (blockVertex block left))
        (tailEmbedding (blockVertex block right)) = _
    rw [tailEmbedding_blockVertex block left hleft,
      tailEmbedding_blockVertex block right hright]
    rw [star_blockSize_tail] at htemplate
    simpa using htemplate

/-- Every full profile-D star selects one of the eight exact tail joins. -/
theorem exists_tailWitness_of_star
    (w : CanonicalStarWitness ProfileD) :
    ∃ kind : Kind, Nonempty (Witness kind) :=
  ⟨kindOfWitness w, ⟨witnessOfStar w⟩⟩

/-- One semantic refutation for each of the eight fixed tail-template
choices.  The fields are propositions and are not asserted by this file. -/
structure Refutations : Prop where
  uuu : ¬Nonempty (Witness .uuu)
  uut : ¬Nonempty (Witness .uut)
  utu : ¬Nonempty (Witness .utu)
  utt : ¬Nonempty (Witness .utt)
  tuu : ¬Nonempty (Witness .tuu)
  tut : ¬Nonempty (Witness .tut)
  ttu : ¬Nonempty (Witness .ttu)
  ttt : ¬Nonempty (Witness .ttt)

theorem Refutations.refutation (h : Refutations) (kind : Kind) :
    ¬Nonempty (Witness kind) := by
  cases kind with
  | uuu => exact h.uuu
  | uut => exact h.uut
  | utu => exact h.utu
  | utt => exact h.utt
  | tuu => exact h.tuu
  | tut => exact h.tut
  | ttu => exact h.ttu
  | ttt => exact h.ttt

/-- Eight exact tail-join refutations eliminate the full profile-D semantic
star branch. -/
theorem no_profileD_star_of_tripleJoinRefutations (h : Refutations) :
    ¬Nonempty (CanonicalStarWitness ProfileD) := by
  rintro ⟨w⟩
  obtain ⟨kind, hwitness⟩ := exists_tailWitness_of_star w
  exact h.refutation kind hwitness

#print axioms R4333.ProfileDTripleJoinReduction.tailEmbedding_blockVertex
#print axioms R4333.ProfileDTripleJoinReduction.witnessOfStar
#print axioms R4333.ProfileDTripleJoinReduction.exists_tailWitness_of_star
#print axioms R4333.ProfileDTripleJoinReduction.no_profileD_star_of_tripleJoinRefutations

end ProfileDTripleJoinReduction

end R4333
