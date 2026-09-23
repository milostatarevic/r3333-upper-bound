import R4333Lean.CriticalTemplateDeletion
import R4333Lean.ProfileDCommonOwnColorColumnCNF
import R4333Lean.ProfileDBlockZeroSupportShadows
import R4333Lean.ProfileDColumnOwnColorIncidence61
import R4333Lean.ProfileDFourRowKindSymmetry

/-!
# Selected-position normal forms in the critical K15 templates

For a distinguished vertex of either fixed critical `K15`, this file gives
an explicit colour-preserving permutation taking it to a small canonical
set of representatives.  Every finite claim below is checked by kernel
reduction against the concrete template tables.

The untwisted template has three normal-form positions, `0`, `1`, and `2`.
The twisted template has nine: `0`, `1`, `2`, `4`, `5`, `6`, `7`, `9`, and
`12`.  We only use the positive normalization statement here: no claim that
different listed representatives lie in different full automorphism orbits
is needed for the quotient.
-/

namespace R4333

/-! ## Explicit permutations -/

def k15PositionIdentity : Fin 15 → Fin 15 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

def k15PositionInvolution : Fin 15 → Fin 15 :=
  ![3, 11, 8, 0, 13, 5, 6, 14, 2, 10, 9, 1, 12, 4, 7]

def k15UntwistedPositionMapFour : Fin 15 → Fin 15 :=
  ![7, 6, 4, 5, 2, 3, 1, 0, 8, 9, 11, 10, 13, 12, 14]

def k15UntwistedPositionMapFive : Fin 15 → Fin 15 :=
  ![5, 9, 2, 14, 12, 0, 11, 7, 13, 1, 10, 6, 4, 8, 3]

def k15UntwistedPositionMapSix : Fin 15 → Fin 15 :=
  ![5, 10, 8, 7, 12, 3, 1, 14, 4, 11, 9, 6, 13, 2, 0]

def k15UntwistedPositionMapSeven : Fin 15 → Fin 15 :=
  ![3, 9, 4, 14, 13, 7, 10, 0, 12, 6, 11, 1, 2, 8, 5]

def k15UntwistedPositionMapTen : Fin 15 → Fin 15 :=
  ![0, 10, 13, 7, 4, 14, 9, 3, 12, 6, 1, 11, 8, 2, 5]

/-- The concrete normalizer chosen for each untwisted selected position. -/
def k15UntwistedSelectedPositionMap : Fin 15 → Fin 15 → Fin 15 :=
  ![k15PositionIdentity,
    k15PositionIdentity,
    k15PositionIdentity,
    k15PositionInvolution,
    k15UntwistedPositionMapFour,
    k15UntwistedPositionMapFive,
    k15UntwistedPositionMapSix,
    k15UntwistedPositionMapSeven,
    k15PositionInvolution,
    k15UntwistedPositionMapFive,
    k15UntwistedPositionMapTen,
    k15UntwistedPositionMapSeven,
    k15UntwistedPositionMapSeven,
    k15UntwistedPositionMapTen,
    k15UntwistedPositionMapSix]

/-- The common involution handles every nontrivial twisted two-point class. -/
def k15TwistedSelectedPositionMap : Fin 15 → Fin 15 → Fin 15 :=
  ![k15PositionIdentity,
    k15PositionIdentity,
    k15PositionIdentity,
    k15PositionInvolution,
    k15PositionIdentity,
    k15PositionIdentity,
    k15PositionIdentity,
    k15PositionIdentity,
    k15PositionInvolution,
    k15PositionIdentity,
    k15PositionInvolution,
    k15PositionInvolution,
    k15PositionIdentity,
    k15PositionInvolution,
    k15PositionInvolution]

/-- A selected-position normalizer for either critical template. -/
def k15SelectedPositionMap
    (twisted : Bool) (selected : Fin 15) : Fin 15 → Fin 15 :=
  if twisted then k15TwistedSelectedPositionMap selected
  else k15UntwistedSelectedPositionMap selected

/-! ## Canonical representatives -/

def k15UntwistedPositionRepresentative : Fin 15 → Fin 15 :=
  ![0, 1, 2, 0, 2, 0, 1, 0, 2, 1, 1, 1, 2, 2, 0]

def k15TwistedPositionRepresentative : Fin 15 → Fin 15 :=
  ![0, 1, 2, 0, 4, 5, 6, 7, 2, 9, 9, 1, 12, 4, 7]

def k15PositionRepresentative
    (twisted : Bool) (selected : Fin 15) : Fin 15 :=
  if twisted then k15TwistedPositionRepresentative selected
  else k15UntwistedPositionRepresentative selected

def k15PositionRepresentativeSet (twisted : Bool) : Finset (Fin 15) :=
  if twisted then {0, 1, 2, 4, 5, 6, 7, 9, 12}
  else {0, 1, 2}

theorem k15UntwistedPositionRepresentative_mem (selected : Fin 15) :
    k15UntwistedPositionRepresentative selected ∈
      ({0, 1, 2} : Finset (Fin 15)) := by
  fin_cases selected <;> decide

theorem k15TwistedPositionRepresentative_mem (selected : Fin 15) :
    k15TwistedPositionRepresentative selected ∈
      ({0, 1, 2, 4, 5, 6, 7, 9, 12} : Finset (Fin 15)) := by
  fin_cases selected <;> decide

theorem k15PositionRepresentative_mem
    (twisted : Bool) (selected : Fin 15) :
    k15PositionRepresentative twisted selected ∈
      k15PositionRepresentativeSet twisted := by
  cases twisted
  · exact k15UntwistedPositionRepresentative_mem selected
  · exact k15TwistedPositionRepresentative_mem selected

theorem k15PositionRepresentativeSet_card (twisted : Bool) :
    (k15PositionRepresentativeSet twisted).card =
      if twisted then 9 else 3 := by
  cases twisted <;> decide

/-! ## Kernel-checked normalization laws -/

set_option maxRecDepth 100000 in
theorem k15SelectedPositionMap_bijective
    (twisted : Bool) (selected : Fin 15) :
    Function.Bijective (k15SelectedPositionMap twisted selected) := by
  cases twisted <;> fin_cases selected <;> decide

noncomputable def k15SelectedPositionEquiv
    (twisted : Bool) (selected : Fin 15) : Fin 15 ≃ Fin 15 :=
  Equiv.ofBijective (k15SelectedPositionMap twisted selected)
    (k15SelectedPositionMap_bijective twisted selected)

@[simp] theorem k15SelectedPositionEquiv_apply
    (twisted : Bool) (selected x : Fin 15) :
    k15SelectedPositionEquiv twisted selected x =
      k15SelectedPositionMap twisted selected x := rfl

set_option maxRecDepth 100000 in
theorem k15SelectedPositionMap_selected
    (twisted : Bool) (selected : Fin 15) :
    k15SelectedPositionMap twisted selected selected =
      k15PositionRepresentative twisted selected := by
  cases twisted <;> fin_cases selected <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15SelectedPositionMap_preserves
    (twisted : Bool) (selected : Fin 15) :
    ∀ u v, u ≠ v →
      k15Template twisted u v =
        k15Template twisted
          (k15SelectedPositionMap twisted selected u)
          (k15SelectedPositionMap twisted selected v) := by
  cases twisted <;> fin_cases selected <;> decide

theorem k15SelectedPositionEquiv_selected
    (twisted : Bool) (selected : Fin 15) :
    k15SelectedPositionEquiv twisted selected selected =
      k15PositionRepresentative twisted selected := by
  rw [k15SelectedPositionEquiv_apply]
  exact k15SelectedPositionMap_selected twisted selected

theorem k15SelectedPositionEquiv_preserves
    (twisted : Bool) (selected : Fin 15) (u v : Fin 15) (huv : u ≠ v) :
    k15Template twisted u v =
      k15Template twisted
        (k15SelectedPositionEquiv twisted selected u)
        (k15SelectedPositionEquiv twisted selected v) := by
  simpa using k15SelectedPositionMap_preserves twisted selected u v huv

/-! ## The already-certified K16 normalization, packaged in the same style -/

theorem exists_k16SelectedPositionNormalization
    (twisted : Bool) (selected : Fin 16) :
    ∃ e : Fin 16 ≃ Fin 16,
      e selected = Fin.last 15 ∧
      ∀ u v, u ≠ v →
        k16Template twisted u v = k16Template twisted (e u) (e v) := by
  refine ⟨k16TemplateToLastEquiv twisted selected, ?_, ?_⟩
  · change k16TemplateToLastMap twisted selected selected = Fin.last 15
    exact k16TemplateToLastMap_deleted twisted selected
  · intro u v huv
    simpa using k16TemplateToLastMap_preserves twisted selected u v huv

/-! ## Blockwise permutations of the profile-D tail -/

namespace ProfileDSelectedPositionTransport

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDFourRowBoundary
open ProfileDRowSupportBounds61

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev FourVertex := ProfileDFourRowBoundary.FourVertex
abbrev FourExtension := ProfileDFourRowBoundary.FourExtension
abbrev DegreeFlooredFourExtension :=
  ProfileDRowSupportBounds61.DegreeFlooredFourExtension
abbrev CommonExtension :=
  ProfileDCommonOwnColorColumnCNF.CommonOwnColorColumnExtension

noncomputable def selectedPositionPermZero
    (kind : Kind) (selected : Fin 15) : Equiv.Perm TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr
        (k15SelectedPositionEquiv (kind.twisted 0) selected)
        (Equiv.refl (Fin 15)))
      (Equiv.refl (Fin 16))).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

noncomputable def selectedPositionPermOne
    (kind : Kind) (selected : Fin 15) : Equiv.Perm TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr
        (Equiv.refl (Fin 15))
        (k15SelectedPositionEquiv (kind.twisted 1) selected))
      (Equiv.refl (Fin 16))).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

noncomputable def selectedPositionPermTwo
    (kind : Kind) (selected : Fin 16) : Equiv.Perm TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr (Equiv.refl (Fin 15)) (Equiv.refl (Fin 15)))
      (k16TemplateToLastEquiv (kind.twisted 2) selected)).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

theorem selectedPositionPermZero_blockZero
    (kind : Kind) (selected position : Fin 15) :
    selectedPositionPermZero kind selected
        (blockVertex 0 position.val) =
      blockVertex 0
        (k15SelectedPositionEquiv (kind.twisted 0) selected position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp only [selectedPositionPermZero, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero _

theorem selectedPositionPermZero_blockOne
    (kind : Kind) (selected position : Fin 15) :
    selectedPositionPermZero kind selected
        (blockVertex 1 position.val) = blockVertex 1 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp [selectedPositionPermZero]

theorem selectedPositionPermZero_blockTwo
    (kind : Kind) (selected : Fin 15) (position : Fin 16) :
    selectedPositionPermZero kind selected
        (blockVertex 2 position.val) = blockVertex 2 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp [selectedPositionPermZero]

theorem selectedPositionPermOne_blockZero
    (kind : Kind) (selected position : Fin 15) :
    selectedPositionPermOne kind selected
        (blockVertex 0 position.val) = blockVertex 0 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp [selectedPositionPermOne]

theorem selectedPositionPermOne_blockOne
    (kind : Kind) (selected position : Fin 15) :
    selectedPositionPermOne kind selected
        (blockVertex 1 position.val) =
      blockVertex 1
        (k15SelectedPositionEquiv (kind.twisted 1) selected position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp only [selectedPositionPermOne, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne _

theorem selectedPositionPermOne_blockTwo
    (kind : Kind) (selected : Fin 15) (position : Fin 16) :
    selectedPositionPermOne kind selected
        (blockVertex 2 position.val) = blockVertex 2 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp [selectedPositionPermOne]

theorem selectedPositionPermTwo_blockZero
    (kind : Kind) (selected : Fin 16) (position : Fin 15) :
    selectedPositionPermTwo kind selected
        (blockVertex 0 position.val) = blockVertex 0 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp [selectedPositionPermTwo]

theorem selectedPositionPermTwo_blockOne
    (kind : Kind) (selected : Fin 16) (position : Fin 15) :
    selectedPositionPermTwo kind selected
        (blockVertex 1 position.val) = blockVertex 1 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp [selectedPositionPermTwo]

theorem selectedPositionPermTwo_blockTwo
    (kind : Kind) (selected position : Fin 16) :
    selectedPositionPermTwo kind selected
        (blockVertex 2 position.val) =
      blockVertex 2
        (k16TemplateToLastEquiv (kind.twisted 2) selected position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp only [selectedPositionPermTwo, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo _

theorem selectedPositionPermZero_symm_blockZero
    (kind : Kind) (selected position : Fin 15) :
    (selectedPositionPermZero kind selected).symm
        (blockVertex 0 position.val) =
      blockVertex 0
        ((k15SelectedPositionEquiv
          (kind.twisted 0) selected).symm position).val := by
  apply (selectedPositionPermZero kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermZero_blockZero]
  simp

theorem selectedPositionPermZero_symm_blockOne
    (kind : Kind) (selected position : Fin 15) :
    (selectedPositionPermZero kind selected).symm
        (blockVertex 1 position.val) = blockVertex 1 position.val := by
  apply (selectedPositionPermZero kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermZero_blockOne]

theorem selectedPositionPermZero_symm_blockTwo
    (kind : Kind) (selected : Fin 15) (position : Fin 16) :
    (selectedPositionPermZero kind selected).symm
        (blockVertex 2 position.val) = blockVertex 2 position.val := by
  apply (selectedPositionPermZero kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermZero_blockTwo]

theorem selectedPositionPermOne_symm_blockZero
    (kind : Kind) (selected position : Fin 15) :
    (selectedPositionPermOne kind selected).symm
        (blockVertex 0 position.val) = blockVertex 0 position.val := by
  apply (selectedPositionPermOne kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermOne_blockZero]

theorem selectedPositionPermOne_symm_blockOne
    (kind : Kind) (selected position : Fin 15) :
    (selectedPositionPermOne kind selected).symm
        (blockVertex 1 position.val) =
      blockVertex 1
        ((k15SelectedPositionEquiv
          (kind.twisted 1) selected).symm position).val := by
  apply (selectedPositionPermOne kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermOne_blockOne]
  simp

theorem selectedPositionPermOne_symm_blockTwo
    (kind : Kind) (selected : Fin 15) (position : Fin 16) :
    (selectedPositionPermOne kind selected).symm
        (blockVertex 2 position.val) = blockVertex 2 position.val := by
  apply (selectedPositionPermOne kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermOne_blockTwo]

theorem selectedPositionPermTwo_symm_blockZero
    (kind : Kind) (selected : Fin 16) (position : Fin 15) :
    (selectedPositionPermTwo kind selected).symm
        (blockVertex 0 position.val) = blockVertex 0 position.val := by
  apply (selectedPositionPermTwo kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermTwo_blockZero]

theorem selectedPositionPermTwo_symm_blockOne
    (kind : Kind) (selected : Fin 16) (position : Fin 15) :
    (selectedPositionPermTwo kind selected).symm
        (blockVertex 1 position.val) = blockVertex 1 position.val := by
  apply (selectedPositionPermTwo kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermTwo_blockOne]

theorem selectedPositionPermTwo_symm_blockTwo
    (kind : Kind) (selected position : Fin 16) :
    (selectedPositionPermTwo kind selected).symm
        (blockVertex 2 position.val) =
      blockVertex 2
        ((k16TemplateToLastEquiv
          (kind.twisted 2) selected).symm position).val := by
  apply (selectedPositionPermTwo kind selected).injective
  rw [Equiv.apply_symm_apply,
    selectedPositionPermTwo_blockTwo]
  simp

/-! ## Canonicality after inverse relabelling -/

theorem selectedPositionPermZero_symm_templateCanonical
    {kind : Kind} (tail : Witness kind) (selected : Fin 15) :
    ∀ (block : Fin 3) (left right : Nat),
      left < ProfileDTripleJoinReduction.blockSize block →
      right < ProfileDTripleJoinReduction.blockSize block → left < right →
      tail.coloring
          ((selectedPositionPermZero kind selected).symm
            (blockVertex block left))
          ((selectedPositionPermZero kind selected).symm
            (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (ProfileDTripleJoinReduction.blockSize block)
            (kind.twisted block) left right) := by
  intro block left right hleft hright hlr
  fin_cases block
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        ((selectedPositionPermZero kind selected).symm
          (blockVertex 0 left))
        ((selectedPositionPermZero kind selected).symm
          (blockVertex 0 right)) =
      canonicalPalette 1
        (templateColor 15 (kind.twisted 0) left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    let e := k15SelectedPositionEquiv (kind.twisted 0) selected
    have hne : leftFin ≠ rightFin :=
      Fin.ne_of_lt (by simpa [leftFin, rightFin] using hlr)
    have hinvne : e.symm leftFin ≠ e.symm rightFin :=
      e.symm.injective.ne hne
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermZero_symm_blockZero,
      selectedPositionPermZero_symm_blockZero]
    calc
      tail.coloring
          (blockVertex 0 (e.symm leftFin).val)
          (blockVertex 0 (e.symm rightFin).val) =
        canonicalPalette (Fin.succ (0 : Fin 3))
          (k15Template (kind.twisted 0)
            (e.symm leftFin) (e.symm rightFin)) :=
        ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
          tail 0 (by rfl) _ _ hinvne
      _ = canonicalPalette (Fin.succ (0 : Fin 3))
          (k15Template (kind.twisted 0) leftFin rightFin) := by
        congr 1
        simpa [e] using
          (k15SelectedPositionEquiv_preserves
            (kind.twisted 0) selected
            (e.symm leftFin) (e.symm rightFin) hinvne)
      _ = canonicalPalette (Fin.succ (0 : Fin 3))
          (templateColor (ProfileDTripleJoinReduction.blockSize 0)
            (kind.twisted 0)
            leftFin.val rightFin.val) := by
        simp [ProfileDTripleJoinReduction.blockSize,
          templateColor, fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt leftFin.isLt,
          Nat.mod_eq_of_lt rightFin.isLt]
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        ((selectedPositionPermZero kind selected).symm
          (blockVertex 1 left))
        ((selectedPositionPermZero kind selected).symm
          (blockVertex 1 right)) =
      canonicalPalette 2
        (templateColor 15 (kind.twisted 1) left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermZero_symm_blockOne,
      selectedPositionPermZero_symm_blockOne]
    simpa [ProfileDTripleJoinReduction.blockSize, leftFin, rightFin] using
      tail.templateCanonical 1 left right hleft hright hlr
  · change left < 16 at hleft
    change right < 16 at hright
    change tail.coloring
        ((selectedPositionPermZero kind selected).symm
          (blockVertex 2 left))
        ((selectedPositionPermZero kind selected).symm
          (blockVertex 2 right)) =
      canonicalPalette 3
        (templateColor 16 (kind.twisted 2) left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermZero_symm_blockTwo,
      selectedPositionPermZero_symm_blockTwo]
    simpa [ProfileDTripleJoinReduction.blockSize, leftFin, rightFin] using
      tail.templateCanonical 2 left right hleft hright hlr

theorem selectedPositionPermOne_symm_templateCanonical
    {kind : Kind} (tail : Witness kind) (selected : Fin 15) :
    ∀ (block : Fin 3) (left right : Nat),
      left < ProfileDTripleJoinReduction.blockSize block →
      right < ProfileDTripleJoinReduction.blockSize block → left < right →
      tail.coloring
          ((selectedPositionPermOne kind selected).symm
            (blockVertex block left))
          ((selectedPositionPermOne kind selected).symm
            (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (ProfileDTripleJoinReduction.blockSize block)
            (kind.twisted block) left right) := by
  intro block left right hleft hright hlr
  fin_cases block
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        ((selectedPositionPermOne kind selected).symm
          (blockVertex 0 left))
        ((selectedPositionPermOne kind selected).symm
          (blockVertex 0 right)) =
      canonicalPalette 1
        (templateColor 15 (kind.twisted 0) left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermOne_symm_blockZero,
      selectedPositionPermOne_symm_blockZero]
    simpa [ProfileDTripleJoinReduction.blockSize, leftFin, rightFin] using
      tail.templateCanonical 0 left right hleft hright hlr
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        ((selectedPositionPermOne kind selected).symm
          (blockVertex 1 left))
        ((selectedPositionPermOne kind selected).symm
          (blockVertex 1 right)) =
      canonicalPalette 2
        (templateColor 15 (kind.twisted 1) left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    let e := k15SelectedPositionEquiv (kind.twisted 1) selected
    have hne : leftFin ≠ rightFin :=
      Fin.ne_of_lt (by simpa [leftFin, rightFin] using hlr)
    have hinvne : e.symm leftFin ≠ e.symm rightFin :=
      e.symm.injective.ne hne
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermOne_symm_blockOne,
      selectedPositionPermOne_symm_blockOne]
    calc
      tail.coloring
          (blockVertex 1 (e.symm leftFin).val)
          (blockVertex 1 (e.symm rightFin).val) =
        canonicalPalette (Fin.succ (1 : Fin 3))
          (k15Template (kind.twisted 1)
            (e.symm leftFin) (e.symm rightFin)) :=
        ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
          tail 1 (by rfl) _ _ hinvne
      _ = canonicalPalette (Fin.succ (1 : Fin 3))
          (k15Template (kind.twisted 1) leftFin rightFin) := by
        congr 1
        simpa [e] using
          (k15SelectedPositionEquiv_preserves
            (kind.twisted 1) selected
            (e.symm leftFin) (e.symm rightFin) hinvne)
      _ = canonicalPalette (Fin.succ (1 : Fin 3))
          (templateColor (ProfileDTripleJoinReduction.blockSize 1)
            (kind.twisted 1) leftFin.val rightFin.val) := by
        simp [ProfileDTripleJoinReduction.blockSize,
          templateColor, fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt leftFin.isLt,
          Nat.mod_eq_of_lt rightFin.isLt]
  · change left < 16 at hleft
    change right < 16 at hright
    change tail.coloring
        ((selectedPositionPermOne kind selected).symm
          (blockVertex 2 left))
        ((selectedPositionPermOne kind selected).symm
          (blockVertex 2 right)) =
      canonicalPalette 3
        (templateColor 16 (kind.twisted 2) left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermOne_symm_blockTwo,
      selectedPositionPermOne_symm_blockTwo]
    simpa [ProfileDTripleJoinReduction.blockSize, leftFin, rightFin] using
      tail.templateCanonical 2 left right hleft hright hlr

theorem selectedPositionPermTwo_symm_templateCanonical
    {kind : Kind} (tail : Witness kind) (selected : Fin 16) :
    ∀ (block : Fin 3) (left right : Nat),
      left < ProfileDTripleJoinReduction.blockSize block →
      right < ProfileDTripleJoinReduction.blockSize block → left < right →
      tail.coloring
          ((selectedPositionPermTwo kind selected).symm
            (blockVertex block left))
          ((selectedPositionPermTwo kind selected).symm
            (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (ProfileDTripleJoinReduction.blockSize block)
            (kind.twisted block) left right) := by
  intro block left right hleft hright hlr
  fin_cases block
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        ((selectedPositionPermTwo kind selected).symm
          (blockVertex 0 left))
        ((selectedPositionPermTwo kind selected).symm
          (blockVertex 0 right)) =
      canonicalPalette 1
        (templateColor 15 (kind.twisted 0) left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermTwo_symm_blockZero,
      selectedPositionPermTwo_symm_blockZero]
    simpa [ProfileDTripleJoinReduction.blockSize, leftFin, rightFin] using
      tail.templateCanonical 0 left right hleft hright hlr
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        ((selectedPositionPermTwo kind selected).symm
          (blockVertex 1 left))
        ((selectedPositionPermTwo kind selected).symm
          (blockVertex 1 right)) =
      canonicalPalette 2
        (templateColor 15 (kind.twisted 1) left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermTwo_symm_blockOne,
      selectedPositionPermTwo_symm_blockOne]
    simpa [ProfileDTripleJoinReduction.blockSize, leftFin, rightFin] using
      tail.templateCanonical 1 left right hleft hright hlr
  · change left < 16 at hleft
    change right < 16 at hright
    change tail.coloring
        ((selectedPositionPermTwo kind selected).symm
          (blockVertex 2 left))
        ((selectedPositionPermTwo kind selected).symm
          (blockVertex 2 right)) =
      canonicalPalette 3
        (templateColor 16 (kind.twisted 2) left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    let e := k16TemplateToLastEquiv (kind.twisted 2) selected
    have hne : leftFin ≠ rightFin :=
      Fin.ne_of_lt (by simpa [leftFin, rightFin] using hlr)
    have hinvne : e.symm leftFin ≠ e.symm rightFin :=
      e.symm.injective.ne hne
    rw [show left = leftFin.val by rfl,
      show right = rightFin.val by rfl,
      selectedPositionPermTwo_symm_blockTwo,
      selectedPositionPermTwo_symm_blockTwo]
    calc
      tail.coloring
          (blockVertex 2 (e.symm leftFin).val)
          (blockVertex 2 (e.symm rightFin).val) =
        canonicalPalette (Fin.succ (2 : Fin 3))
          (k16Template (kind.twisted 2)
            (e.symm leftFin) (e.symm rightFin)) :=
        ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
          tail 2 (by rfl) _ _ hinvne
      _ = canonicalPalette (Fin.succ (2 : Fin 3))
          (k16Template (kind.twisted 2) leftFin rightFin) := by
        congr 1
        have hp := k16TemplateToLastMap_preserves
          (kind.twisted 2) selected
          (e.symm leftFin) (e.symm rightFin) hinvne
        rw [← k16TemplateToLastEquiv_apply,
          ← k16TemplateToLastEquiv_apply] at hp
        simpa [e] using hp
      _ = canonicalPalette (Fin.succ (2 : Fin 3))
          (templateColor (ProfileDTripleJoinReduction.blockSize 2)
            (kind.twisted 2) leftFin.val rightFin.val) := by
        simp [ProfileDTripleJoinReduction.blockSize,
          templateColor, fin16, leftFin, rightFin,
          Nat.mod_eq_of_lt leftFin.isLt,
          Nat.mod_eq_of_lt rightFin.isLt]

/-! ## Generic semantic transport by a certified tail relabelling -/

noncomputable def transportWitnessByTailPerm {kind : Kind}
    (tail : Witness kind) (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (block : Fin 3) (left right : Nat),
      left < ProfileDTripleJoinReduction.blockSize block →
      right < ProfileDTripleJoinReduction.blockSize block → left < right →
      tail.coloring (perm (blockVertex block left))
          (perm (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (ProfileDTripleJoinReduction.blockSize block)
            (kind.twisted block) left right)) : Witness kind where
  coloring := relabelVertices tail.coloring perm
  noMono := noMono_relabelVertices _ _ tail.noMono
  templateCanonical := by
    intro block left right hleft hright hlr
    simpa using hcanonical block left right hleft hright hlr

noncomputable def transportFourExtensionByTailPerm {kind : Kind}
    (ext : FourExtension kind) (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (block : Fin 3) (left right : Nat),
      left < ProfileDTripleJoinReduction.blockSize block →
      right < ProfileDTripleJoinReduction.blockSize block → left < right →
      ext.tail.coloring (perm (blockVertex block left))
          (perm (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (ProfileDTripleJoinReduction.blockSize block)
            (kind.twisted block) left right)) : FourExtension kind where
  tail := transportWitnessByTailPerm ext.tail perm hcanonical
  inside := ext.inside
  rows := fun row x => ext.rows row (perm x)
  insideNoMono := ext.insideNoMono
  insideRootForbidden := ext.insideRootForbidden
  rowsAdmissible := by
    intro row x y hxy hbad
    apply ext.rowsAdmissible row (perm x) (perm y) (perm.injective.ne hxy)
    simpa [transportWitnessByTailPerm] using hbad
  rowsPairCompatible := by
    intro left right hlr x hbad
    exact ext.rowsPairCompatible left right hlr (perm x) hbad

theorem transportFourExtensionByTailPerm_rowSupport_card
    {kind : Kind} (ext : FourExtension kind)
    (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (block : Fin 3) (left right : Nat),
      left < ProfileDTripleJoinReduction.blockSize block →
      right < ProfileDTripleJoinReduction.blockSize block → left < right →
      ext.tail.coloring (perm (blockVertex block left))
          (perm (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (ProfileDTripleJoinReduction.blockSize block)
            (kind.twisted block) left right))
    (row : FourVertex) (q : Fin 4) :
    (rowColorSupport
      ((transportFourExtensionByTailPerm ext perm hcanonical).rows row) q).card =
      (rowColorSupport (ext.rows row) q).card := by
  simpa [transportFourExtensionByTailPerm, Function.comp_def] using
    (ProfileDBlockZeroSupport.rowColorSupport_card_comp_equiv
      perm (ext.rows row) q)

noncomputable def transportDegreeFlooredByTailPerm {kind : Kind}
    (ext : DegreeFlooredFourExtension kind)
    (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (block : Fin 3) (left right : Nat),
      left < ProfileDTripleJoinReduction.blockSize block →
      right < ProfileDTripleJoinReduction.blockSize block → left < right →
      ext.toFourExtension.tail.coloring (perm (blockVertex block left))
          (perm (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (ProfileDTripleJoinReduction.blockSize block)
            (kind.twisted block) left right)) :
    DegreeFlooredFourExtension kind where
  toFourExtension :=
    transportFourExtensionByTailPerm ext.toFourExtension perm hcanonical
  zeroSupportLower := by
    intro row
    rw [transportFourExtensionByTailPerm_rowSupport_card]
    exact ext.zeroSupportLower row
  zeroSupportUpper := by
    intro row
    rw [transportFourExtensionByTailPerm_rowSupport_card]
    exact ext.zeroSupportUpper row
  nonzeroSupportLower := by
    intro row q hq
    rw [transportFourExtensionByTailPerm_rowSupport_card]
    exact ext.nonzeroSupportLower row q hq
  nonzeroSupportUpper := by
    intro row q hq
    rw [transportFourExtensionByTailPerm_rowSupport_card]
    exact ext.nonzeroSupportUpper row q hq

noncomputable def normalizeDegreeFlooredBlockZero {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (selected : Fin 15) :
    DegreeFlooredFourExtension kind :=
  transportDegreeFlooredByTailPerm ext
    (selectedPositionPermZero kind selected).symm
    (selectedPositionPermZero_symm_templateCanonical
      ext.toFourExtension.tail selected)

noncomputable def normalizeDegreeFlooredBlockOne {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (selected : Fin 15) :
    DegreeFlooredFourExtension kind :=
  transportDegreeFlooredByTailPerm ext
    (selectedPositionPermOne kind selected).symm
    (selectedPositionPermOne_symm_templateCanonical
      ext.toFourExtension.tail selected)

noncomputable def normalizeDegreeFlooredBlockTwo {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (selected : Fin 16) :
    DegreeFlooredFourExtension kind :=
  transportDegreeFlooredByTailPerm ext
    (selectedPositionPermTwo kind selected).symm
    (selectedPositionPermTwo_symm_templateCanonical
      ext.toFourExtension.tail selected)

/-! ## Transporting a common own-colour column to its normal form -/

noncomputable def normalizeCommonBlockZero {kind : Kind}
    (ext : CommonExtension kind) (selected : Fin 15)
    (hcolumn : ext.column = blockVertex 0 selected.val) :
    CommonExtension kind where
  toDegreeFlooredFourExtension :=
    normalizeDegreeFlooredBlockZero
      ext.toDegreeFlooredFourExtension selected
  column := blockVertex 0
    (k15PositionRepresentative (kind.twisted 0) selected).val
  columnOwnColor := by
    intro row
    let forward := selectedPositionPermZero kind selected
    have hforward :
        forward (blockVertex 0 selected.val) =
          blockVertex 0
            (k15PositionRepresentative (kind.twisted 0) selected).val := by
      rw [selectedPositionPermZero_blockZero,
        k15SelectedPositionEquiv_selected]
    change ext.toDegreeFlooredFourExtension.toFourExtension.rows row
        (forward.symm
          (blockVertex 0
            (k15PositionRepresentative (kind.twisted 0) selected).val)) =
      ProfileDFourRowDegreeCap.tailRootColor
        (blockVertex 0
          (k15PositionRepresentative (kind.twisted 0) selected).val)
    have hinverse :
        forward.symm
            (blockVertex 0
              (k15PositionRepresentative (kind.twisted 0) selected).val) =
          blockVertex 0 selected.val := by
      rw [← hforward, Equiv.symm_apply_apply]
    rw [hinverse]
    have hold := ext.columnOwnColor row
    rw [hcolumn] at hold
    rw [ProfileDColumnOwnColorIncidence61.tailRootColor_blockVertex] at hold ⊢
    exact hold

noncomputable def normalizeCommonBlockOne {kind : Kind}
    (ext : CommonExtension kind) (selected : Fin 15)
    (hcolumn : ext.column = blockVertex 1 selected.val) :
    CommonExtension kind where
  toDegreeFlooredFourExtension :=
    normalizeDegreeFlooredBlockOne
      ext.toDegreeFlooredFourExtension selected
  column := blockVertex 1
    (k15PositionRepresentative (kind.twisted 1) selected).val
  columnOwnColor := by
    intro row
    let forward := selectedPositionPermOne kind selected
    have hforward :
        forward (blockVertex 1 selected.val) =
          blockVertex 1
            (k15PositionRepresentative (kind.twisted 1) selected).val := by
      rw [selectedPositionPermOne_blockOne,
        k15SelectedPositionEquiv_selected]
    change ext.toDegreeFlooredFourExtension.toFourExtension.rows row
        (forward.symm
          (blockVertex 1
            (k15PositionRepresentative (kind.twisted 1) selected).val)) =
      ProfileDFourRowDegreeCap.tailRootColor
        (blockVertex 1
          (k15PositionRepresentative (kind.twisted 1) selected).val)
    have hinverse :
        forward.symm
            (blockVertex 1
              (k15PositionRepresentative (kind.twisted 1) selected).val) =
          blockVertex 1 selected.val := by
      rw [← hforward, Equiv.symm_apply_apply]
    rw [hinverse]
    have hold := ext.columnOwnColor row
    rw [hcolumn] at hold
    rw [ProfileDColumnOwnColorIncidence61.tailRootColor_blockVertex] at hold ⊢
    exact hold

noncomputable def normalizeCommonBlockTwo {kind : Kind}
    (ext : CommonExtension kind) (selected : Fin 16)
    (hcolumn : ext.column = blockVertex 2 selected.val) :
    CommonExtension kind where
  toDegreeFlooredFourExtension :=
    normalizeDegreeFlooredBlockTwo
      ext.toDegreeFlooredFourExtension selected
  column := blockVertex 2 (Fin.last 15).val
  columnOwnColor := by
    intro row
    let forward := selectedPositionPermTwo kind selected
    have hforward :
        forward (blockVertex 2 selected.val) =
          blockVertex 2 (Fin.last 15).val := by
      rw [selectedPositionPermTwo_blockTwo,
        k16TemplateToLastEquiv_apply,
        k16TemplateToLastMap_deleted]
    change ext.toDegreeFlooredFourExtension.toFourExtension.rows row
        (forward.symm (blockVertex 2 (Fin.last 15).val)) =
      ProfileDFourRowDegreeCap.tailRootColor
        (blockVertex 2 (Fin.last 15).val)
    have hinverse :
        forward.symm (blockVertex 2 (Fin.last 15).val) =
          blockVertex 2 selected.val := by
      rw [← hforward, Equiv.symm_apply_apply]
    rw [hinverse]
    have hold := ext.columnOwnColor row
    rw [hcolumn] at hold
    rw [ProfileDColumnOwnColorIncidence61.tailRootColor_blockVertex] at hold ⊢
    exact hold

/-- The finite selected-column quotient used by the common-column boundary:
three positions for an untwisted K15 block, nine for a twisted K15 block,
and one position for the vertex-transitive K16 block. -/
def IsCanonicalCommonColumn (kind : Kind) (column : TailVertex) : Prop :=
  (∃ position : Fin 15,
    position ∈ k15PositionRepresentativeSet (kind.twisted 0) ∧
    column = blockVertex 0 position.val) ∨
  (∃ position : Fin 15,
    position ∈ k15PositionRepresentativeSet (kind.twisted 1) ∧
    column = blockVertex 1 position.val) ∨
  column = blockVertex 2 (Fin.last 15).val

theorem exists_normalizedCommonExtension {kind : Kind}
    (ext : CommonExtension kind) :
    ∃ normalized : CommonExtension kind,
      IsCanonicalCommonColumn kind normalized.column := by
  generalize hcoord :
    ProfileDFourRowKindSymmetry.tailDecompEquiv.symm ext.column = coord
  have hcolumn :
      ext.column = ProfileDFourRowKindSymmetry.tailDecompEquiv coord := by
    have h := congrArg ProfileDFourRowKindSymmetry.tailDecompEquiv hcoord
    simpa using h
  cases coord with
  | inl pair =>
      cases pair with
      | inl selected =>
          have hzero : ext.column = blockVertex 0 selected.val :=
            hcolumn.trans
              (ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero selected)
          refine ⟨normalizeCommonBlockZero ext selected hzero, ?_⟩
          exact Or.inl ⟨_, k15PositionRepresentative_mem _ selected, rfl⟩
      | inr selected =>
          have hone : ext.column = blockVertex 1 selected.val :=
            hcolumn.trans
              (ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne selected)
          refine ⟨normalizeCommonBlockOne ext selected hone, ?_⟩
          exact Or.inr (Or.inl
            ⟨_, k15PositionRepresentative_mem _ selected, rfl⟩)
  | inr selected =>
      have htwo : ext.column = blockVertex 2 selected.val :=
        hcolumn.trans
          (ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo selected)
      refine ⟨normalizeCommonBlockTwo ext selected htwo, ?_⟩
      exact Or.inr (Or.inr rfl)

end ProfileDSelectedPositionTransport

#print axioms R4333.k15SelectedPositionMap_bijective
#print axioms R4333.k15SelectedPositionMap_selected
#print axioms R4333.k15SelectedPositionMap_preserves
#print axioms R4333.exists_k16SelectedPositionNormalization
#print axioms R4333.ProfileDSelectedPositionTransport.transportDegreeFlooredByTailPerm
#print axioms R4333.ProfileDSelectedPositionTransport.exists_normalizedCommonExtension

end R4333
