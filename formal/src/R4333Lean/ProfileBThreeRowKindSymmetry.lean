import R4333Lean.ProfileBThreeRowBoundary
import R4333Lean.ColorRelabel
import R4333Lean.CriticalTemplatePaletteSymmetry

/-!
# Genuine kind symmetry for the profile-B three-row boundary

The last two tail blocks in profile B are both critical `K16`s.  Swapping
those two blocks and globally swapping host colours `2` and `3` preserves
the exact three-row extension problem.  The first tail block is a `K15` and
is left in place.  Its host colour is `1`, but its internal canonical
palette uses colours `2` and `3`; the checked full-palette automorphism of
the critical `K15` is therefore used to compensate for their global swap.

This is a semantic transport of tail colourings, inside edges, and all
three rows.  It reduces the eight selector kinds to six representatives.
No finite-search result is asserted here.
-/

namespace R4333
namespace ProfileBThreeRowKindSymmetry

open SingleRootStarCNF
open ProfileBRowExtension
open ProfileBThreeRowBoundary
open ColoringJoinRows

/-! ## The two involutions -/

/-- Exchange the two equal `K16` blocks, leaving the `K15` block fixed. -/
def blockSwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

@[simp] theorem blockSwap_zero : blockSwap 0 = 0 := by decide
@[simp] theorem blockSwap_one : blockSwap 1 = 2 := by decide
@[simp] theorem blockSwap_two : blockSwap 2 = 1 := by decide

/-- Exchange their omitted host colours.  Colours zero and one are fixed. -/
def hostColorSwap : Equiv.Perm (Fin 4) := Equiv.swap 2 3

@[simp] theorem hostColorSwap_zero : hostColorSwap 0 = 0 := by decide
@[simp] theorem hostColorSwap_one : hostColorSwap 1 = 1 := by decide
@[simp] theorem hostColorSwap_two : hostColorSwap 2 = 3 := by decide
@[simp] theorem hostColorSwap_three : hostColorSwap 3 = 2 := by decide

/-- On the local palette of the fixed `K15`, the same operation exchanges
local colours one and two. -/
def k15LabelSwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

@[simp] theorem k15LabelSwap_zero : k15LabelSwap 0 = 0 := by decide
@[simp] theorem k15LabelSwap_one : k15LabelSwap 1 = 2 := by decide
@[simp] theorem k15LabelSwap_two : k15LabelSwap 2 = 1 := by decide

/-- Swap the two `K16` selector bits while retaining the `K15` bit. -/
def swapKind (kind : Kind) : Kind :=
  Kind.ofBooleans (kind.twisted 0) (kind.twisted 2) (kind.twisted 1)

@[simp] theorem swapKind_twisted_zero (kind : Kind) :
    (swapKind kind).twisted 0 = kind.twisted 0 := by
  simp [swapKind]

@[simp] theorem swapKind_twisted_one (kind : Kind) :
    (swapKind kind).twisted 1 = kind.twisted 2 := by
  simp [swapKind]

@[simp] theorem swapKind_twisted_two (kind : Kind) :
    (swapKind kind).twisted 2 = kind.twisted 1 := by
  simp [swapKind]

@[simp] theorem swapKind_involutive (kind : Kind) :
    swapKind (swapKind kind) = kind := by
  cases kind <;> rfl

/-! ## Checked local palette compensation in the fixed K15 -/

/-- A vertex automorphism supplied by the kernel-checked full palette
symmetry theorem for the critical `K15`. -/
noncomputable def k15VertexPerm (kind : Kind) : Equiv.Perm (Fin 15) :=
  Classical.choose
    (k15Template_fullPaletteSymmetry (kind.twisted 0) k15LabelSwap)

theorem k15VertexPerm_preserves (kind : Kind) (left right : Fin 15)
    (hlr : left ≠ right) :
    k15Template (kind.twisted 0)
        (k15VertexPerm kind left) (k15VertexPerm kind right) =
      k15LabelSwap (k15Template (kind.twisted 0) left right) :=
  (Classical.choose_spec
    (k15Template_fullPaletteSymmetry
      (kind.twisted 0) k15LabelSwap)) left right hlr

theorem hostColorSwap_canonicalPalette_k15 (q : Fin 3) :
    hostColorSwap (canonicalPalette 1 (k15LabelSwap q)) =
      canonicalPalette 1 q := by
  fin_cases q <;> decide

theorem hostColorSwap_canonicalPalette_k16_left (q : Fin 3) :
    hostColorSwap (canonicalPalette 3 q) = canonicalPalette 2 q := by
  fin_cases q <;> decide

theorem hostColorSwap_canonicalPalette_k16_right (q : Fin 3) :
    hostColorSwap (canonicalPalette 2 q) = canonicalPalette 3 q := by
  fin_cases q <;> decide

/-! ## The 47-vertex tail permutation -/

/-- Decode the contiguous tail as `K15 + K16 + K16`. -/
def tailDecode : TailVertex ≃ Sum (Fin 15) (Sum (Fin 16) (Fin 16)) :=
  (finSumFinEquiv : Sum (Fin 15) (Fin 32) ≃ Fin 47).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin 15))
      (finSumFinEquiv : Sum (Fin 16) (Fin 16) ≃ Fin 32).symm)

@[simp] theorem tailDecode_block_zero (position : Fin 15) :
    tailDecode (blockVertex 0 position.val) = Sum.inl position := by
  have hv : blockVertex 0 position.val = Fin.castAdd 32 position := by
    apply Fin.ext
    simp [ProfileBRowExtension.blockVertex, ProfileBRowExtension.blockStart,
      Nat.mod_eq_of_lt (by omega : position.val < 47)]
  rw [hv]
  change (Equiv.sumCongr (Equiv.refl (Fin 15))
    (finSumFinEquiv : Sum (Fin 16) (Fin 16) ≃ Fin 32).symm)
      ((finSumFinEquiv : Sum (Fin 15) (Fin 32) ≃ Fin 47).symm
        (Fin.castAdd 32 position)) = Sum.inl position
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem tailDecode_block_one (position : Fin 16) :
    tailDecode (blockVertex 1 position.val) =
      Sum.inr (Sum.inl position) := by
  have hv : blockVertex 1 position.val =
      Fin.natAdd 15 (Fin.castAdd 16 position) := by
    apply Fin.ext
    simp [ProfileBRowExtension.blockVertex, ProfileBRowExtension.blockStart,
      Nat.mod_eq_of_lt (by omega : 15 + position.val < 47)]
  rw [hv]
  change (Equiv.sumCongr (Equiv.refl (Fin 15))
    (finSumFinEquiv : Sum (Fin 16) (Fin 16) ≃ Fin 32).symm)
      ((finSumFinEquiv : Sum (Fin 15) (Fin 32) ≃ Fin 47).symm
        (Fin.natAdd 15 (Fin.castAdd 16 position))) =
          Sum.inr (Sum.inl position)
  rw [finSumFinEquiv_symm_apply_natAdd]
  change Sum.inr
    ((finSumFinEquiv : Sum (Fin 16) (Fin 16) ≃ Fin 32).symm
      (Fin.castAdd 16 position)) = Sum.inr (Sum.inl position)
  rw [finSumFinEquiv_symm_apply_castAdd]

@[simp] theorem tailDecode_block_two (position : Fin 16) :
    tailDecode (blockVertex 2 position.val) =
      Sum.inr (Sum.inr position) := by
  have hv : blockVertex 2 position.val =
      Fin.natAdd 15 (Fin.natAdd 16 position) := by
    apply Fin.ext
    simp [ProfileBRowExtension.blockVertex, ProfileBRowExtension.blockStart,
      Nat.mod_eq_of_lt (by omega : 31 + position.val < 47)]
    omega
  rw [hv]
  change (Equiv.sumCongr (Equiv.refl (Fin 15))
    (finSumFinEquiv : Sum (Fin 16) (Fin 16) ≃ Fin 32).symm)
      ((finSumFinEquiv : Sum (Fin 15) (Fin 32) ≃ Fin 47).symm
        (Fin.natAdd 15 (Fin.natAdd 16 position))) =
          Sum.inr (Sum.inr position)
  rw [finSumFinEquiv_symm_apply_natAdd]
  change Sum.inr
    ((finSumFinEquiv : Sum (Fin 16) (Fin 16) ≃ Fin 32).symm
      (Fin.natAdd 16 position)) = Sum.inr (Sum.inr position)
  rw [finSumFinEquiv_symm_apply_natAdd]

/-- Swap the two `K16` summands and apply the compensating automorphism to
the fixed `K15` summand.  The map is oriented from target labels to source
labels, as required by pullback of an edge colouring. -/
noncomputable def decodedTailPerm (kind : Kind) :
    Equiv.Perm (Sum (Fin 15) (Sum (Fin 16) (Fin 16))) where
  toFun
    | .inl x => .inl (k15VertexPerm kind x)
    | .inr (.inl x) => .inr (.inr x)
    | .inr (.inr x) => .inr (.inl x)
  invFun
    | .inl x => .inl ((k15VertexPerm kind).symm x)
    | .inr (.inl x) => .inr (.inr x)
    | .inr (.inr x) => .inr (.inl x)
  left_inv x := by
    rcases x with x | x
    · simp
    · rcases x with x | x <;> simp
  right_inv x := by
    rcases x with x | x
    · simp
    · rcases x with x | x <;> simp

/-- The induced permutation of `Fin 47`. -/
noncomputable def tailVertexPerm (kind : Kind) : Equiv.Perm TailVertex :=
  tailDecode.trans ((decodedTailPerm kind).trans tailDecode.symm)

@[simp] theorem tailVertexPerm_block_zero (kind : Kind) (position : Fin 15) :
    tailVertexPerm kind (blockVertex 0 position.val) =
      blockVertex 0 (k15VertexPerm kind position).val := by
  apply tailDecode.injective
  simp [tailVertexPerm, decodedTailPerm]

@[simp] theorem tailVertexPerm_block_one (kind : Kind) (position : Fin 16) :
    tailVertexPerm kind (blockVertex 1 position.val) =
      blockVertex 2 position.val := by
  apply tailDecode.injective
  simp [tailVertexPerm, decodedTailPerm]

@[simp] theorem tailVertexPerm_block_two (kind : Kind) (position : Fin 16) :
    tailVertexPerm kind (blockVertex 2 position.val) =
      blockVertex 1 position.val := by
  apply tailDecode.injective
  simp [tailVertexPerm, decodedTailPerm]

/-! ## Order-free internal template lemmas -/

theorem tail_k15_internal {kind : Kind} (tail : TailWitness kind)
    (left right : Fin 15) (hlr : left ≠ right) :
    tail.coloring (blockVertex 0 left.val) (blockVertex 0 right.val) =
      canonicalPalette 1 (k15Template (kind.twisted 0) left right) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hlr) with hlt | hgt
  · have h := tail.templateCanonical 0 (by decide)
      left.val right.val left.isLt right.isLt hlt
    have hleft : fin15 left.val = left := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt left.isLt
    have hright : fin15 right.val = right := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt right.isLt
    simpa [ProfileBRowExtension.blockSize, templateColor, hleft, hright] using h
  · rw [tail.coloring.color_symm]
    have h := tail.templateCanonical 0 (by decide)
      right.val left.val right.isLt left.isLt hgt
    have hleft : fin15 left.val = left := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt left.isLt
    have hright : fin15 right.val = right := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt right.isLt
    rw [(k15Template (kind.twisted 0)).color_symm]
    simpa [ProfileBRowExtension.blockSize, templateColor, hleft, hright] using h

theorem tail_k16_one_internal {kind : Kind} (tail : TailWitness kind)
    (left right : Fin 16) (hlr : left ≠ right) :
    tail.coloring (blockVertex 1 left.val) (blockVertex 1 right.val) =
      canonicalPalette 2 (k16Template (kind.twisted 1) left right) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hlr) with hlt | hgt
  · have h := tail.templateCanonical 1 (by decide)
      left.val right.val left.isLt right.isLt hlt
    have hleft : fin16 left.val = left := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt left.isLt
    have hright : fin16 right.val = right := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt right.isLt
    simpa [ProfileBRowExtension.blockSize, templateColor, hleft, hright] using h
  · rw [tail.coloring.color_symm]
    have h := tail.templateCanonical 1 (by decide)
      right.val left.val right.isLt left.isLt hgt
    have hleft : fin16 left.val = left := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt left.isLt
    have hright : fin16 right.val = right := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt right.isLt
    rw [(k16Template (kind.twisted 1)).color_symm]
    simpa [ProfileBRowExtension.blockSize, templateColor, hleft, hright] using h

theorem tail_k16_two_internal {kind : Kind} (tail : TailWitness kind)
    (left right : Fin 16) (hlr : left ≠ right) :
    tail.coloring (blockVertex 2 left.val) (blockVertex 2 right.val) =
      canonicalPalette 3 (k16Template (kind.twisted 2) left right) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hlr) with hlt | hgt
  · have h := tail.templateCanonical 2 (by decide)
      left.val right.val left.isLt right.isLt hlt
    have hleft : fin16 left.val = left := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt left.isLt
    have hright : fin16 right.val = right := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt right.isLt
    simpa [ProfileBRowExtension.blockSize, templateColor, hleft, hright] using h
  · rw [tail.coloring.color_symm]
    have h := tail.templateCanonical 2 (by decide)
      right.val left.val right.isLt left.isLt hgt
    have hleft : fin16 left.val = left := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt left.isLt
    have hright : fin16 right.val = right := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt right.isLt
    rw [(k16Template (kind.twisted 2)).color_symm]
    simpa [ProfileBRowExtension.blockSize, templateColor, hleft, hright] using h

/-! ## Transport of the exact tail -/

noncomputable def transportedTailColoring {kind : Kind}
    (tail : TailWitness kind) : EdgeColoring TailVertex (Fin 4) :=
  mapEdgeColors
    (relabelVertices tail.coloring (tailVertexPerm kind)) hostColorSwap

theorem transported_k15_internal {kind : Kind} (tail : TailWitness kind)
    (left right : Fin 15) (hlr : left ≠ right) :
    transportedTailColoring tail
        (blockVertex 0 left.val) (blockVertex 0 right.val) =
      canonicalPalette 1 (k15Template (kind.twisted 0) left right) := by
  rw [transportedTailColoring, mapEdgeColors_apply, relabelVertices_apply,
    tailVertexPerm_block_zero, tailVertexPerm_block_zero]
  rw [tail_k15_internal tail _ _
    ((k15VertexPerm kind).injective.ne hlr)]
  rw [k15VertexPerm_preserves kind left right hlr]
  exact hostColorSwap_canonicalPalette_k15 _

theorem transported_k16_one_internal {kind : Kind} (tail : TailWitness kind)
    (left right : Fin 16) (hlr : left ≠ right) :
    transportedTailColoring tail
        (blockVertex 1 left.val) (blockVertex 1 right.val) =
      canonicalPalette 2 (k16Template (kind.twisted 2) left right) := by
  rw [transportedTailColoring, mapEdgeColors_apply, relabelVertices_apply,
    tailVertexPerm_block_one, tailVertexPerm_block_one]
  rw [tail_k16_two_internal tail left right hlr]
  exact hostColorSwap_canonicalPalette_k16_left _

theorem transported_k16_two_internal {kind : Kind} (tail : TailWitness kind)
    (left right : Fin 16) (hlr : left ≠ right) :
    transportedTailColoring tail
        (blockVertex 2 left.val) (blockVertex 2 right.val) =
      canonicalPalette 3 (k16Template (kind.twisted 1) left right) := by
  rw [transportedTailColoring, mapEdgeColors_apply, relabelVertices_apply,
    tailVertexPerm_block_two, tailVertexPerm_block_two]
  rw [tail_k16_one_internal tail left right hlr]
  exact hostColorSwap_canonicalPalette_k16_right _

/-- The genuine tail transport.  It swaps the two K16 fibres, transports
every cross-fibre colour globally, and retains the exact canonical template
equations in all three blocks. -/
noncomputable def transportTailWitness {kind : Kind}
    (tail : TailWitness kind) : TailWitness (swapKind kind) where
  coloring := transportedTailColoring tail
  noMono := noMono_mapEdgeColors _ _
    (noMono_relabelVertices _ _ tail.noMono)
  rootForbidden := by
    intro block left right hleft hright hlr
    fin_cases block
    · let leftFin : Fin 15 := ⟨left, by
        simpa [ProfileBRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 15 := ⟨right, by
        simpa [ProfileBRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
        simpa [leftFin, rightFin] using hlr)
      simp at hleft hright ⊢
      rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
        transported_k15_internal tail leftFin rightFin hne]
      exact SingleRootStarWitness61.canonicalPalette_ne_block 1 _
    · let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileBRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileBRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
        simpa [leftFin, rightFin] using hlr)
      simp at hleft hright ⊢
      rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
        transported_k16_one_internal tail leftFin rightFin hne]
      exact SingleRootStarWitness61.canonicalPalette_ne_block 2 _
    · let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileBRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileBRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
        simpa [leftFin, rightFin] using hlr)
      simp at hleft hright ⊢
      rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
        transported_k16_two_internal tail leftFin rightFin hne]
      exact SingleRootStarWitness61.canonicalPalette_ne_block 3 _
  templateCanonical := by
    intro block _ left right hleft hright hlr
    fin_cases block
    · let leftFin : Fin 15 := ⟨left, by
        simpa [ProfileBRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 15 := ⟨right, by
        simpa [ProfileBRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
        simpa [leftFin, rightFin] using hlr)
      simp at hleft hright ⊢
      rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
        transported_k15_internal tail leftFin rightFin hne]
      simp [ProfileBRowExtension.blockSize, templateColor, fin15,
        Nat.mod_eq_of_lt]
    · let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileBRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileBRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
        simpa [leftFin, rightFin] using hlr)
      simp at hleft hright ⊢
      rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
        transported_k16_one_internal tail leftFin rightFin hne]
      simp [ProfileBRowExtension.blockSize, templateColor, fin16,
        Nat.mod_eq_of_lt]

    · let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileBRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileBRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
        simpa [leftFin, rightFin] using hlr)
      simp at hleft hright ⊢
      rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
        transported_k16_two_internal tail leftFin rightFin hne]
      simp [ProfileBRowExtension.blockSize, templateColor, fin16,
        Nat.mod_eq_of_lt]

/-! ## Transport of the full threshold object -/

/-- Transport all three rows and their inside edges along the same global
colour equivalence and tail permutation. -/
noncomputable def transportThreeExtension {kind : Kind}
    (ext : ThreeExtension kind) : ThreeExtension (swapKind kind) where
  tail := transportTailWitness ext.tail
  inside := mapEdgeColors ext.inside hostColorSwap
  rows := fun a x => hostColorSwap (ext.rows a (tailVertexPerm kind x))
  insideNoMono := noMono_mapEdgeColors _ _ ext.insideNoMono
  insideRootForbidden := by
    intro a b hab hzero
    apply ext.insideRootForbidden a b hab
    apply hostColorSwap.injective
    simpa using hzero
  rowsAdmissible := by
    intro a x y hxy hbad
    apply ext.rowsAdmissible a
      (tailVertexPerm kind x) (tailVertexPerm kind y)
      ((tailVertexPerm kind).injective.ne hxy)
    exact ⟨hostColorSwap.injective hbad.1,
      hostColorSwap.injective hbad.2⟩
  rowsPairCompatible := by
    intro a b hab x hbad
    apply ext.rowsPairCompatible a b hab (tailVertexPerm kind x)
    exact ⟨hostColorSwap.injective hbad.1,
      hostColorSwap.injective hbad.2⟩

theorem nonempty_transportThreeExtension {kind : Kind} :
    Nonempty (ThreeExtension kind) →
      Nonempty (ThreeExtension (swapKind kind)) := by
  rintro ⟨ext⟩
  exact ⟨transportThreeExtension ext⟩

/-- Existence is genuinely equivalent for kinds related by exchange of the
two K16 selector bits. -/
theorem nonempty_threeExtension_iff_swapKind (kind : Kind) :
    Nonempty (ThreeExtension kind) ↔
      Nonempty (ThreeExtension (swapKind kind)) := by
  constructor
  · exact nonempty_transportThreeExtension
  · intro h
    have hback := nonempty_transportThreeExtension h
    simpa using hback

/-! ## Six representatives -/

/-- Canonical representative after forgetting the order of the two K16
selector bits. -/
def representativeKind : Kind → Kind
  | .uuu => .uuu
  | .uut | .utu => .uut
  | .utt => .utt
  | .tuu => .tuu
  | .tut | .ttu => .tut
  | .ttt => .ttt

@[simp] theorem representativeKind_swapKind (kind : Kind) :
    representativeKind (swapKind kind) = representativeKind kind := by
  cases kind <;> rfl

theorem nonempty_threeExtension_representative (kind : Kind) :
    Nonempty (ThreeExtension kind) →
      Nonempty (ThreeExtension (representativeKind kind)) := by
  cases kind with
  | uuu => exact id
  | uut => exact id
  | utu => simpa [representativeKind, swapKind, Kind.twisted,
      Kind.ofBooleans] using
      (nonempty_transportThreeExtension (kind := Kind.utu))
  | utt => exact id
  | tuu => exact id
  | tut => exact id
  | ttu => simpa [representativeKind, swapKind, Kind.twisted,
      Kind.ofBooleans] using
      (nonempty_transportThreeExtension (kind := Kind.ttu))
  | ttt => exact id

/-- One obstruction for each orbit under the genuine K16-block swap. -/
structure SixRepresentativeObstructions : Prop where
  uuu : ¬Nonempty (ThreeExtension .uuu)
  uut : ¬Nonempty (ThreeExtension .uut)
  utt : ¬Nonempty (ThreeExtension .utt)
  tuu : ¬Nonempty (ThreeExtension .tuu)
  tut : ¬Nonempty (ThreeExtension .tut)
  ttt : ¬Nonempty (ThreeExtension .ttt)

theorem SixRepresentativeObstructions.refutesRepresentative
    (h : SixRepresentativeObstructions) (kind : Kind) :
    ¬Nonempty (ThreeExtension (representativeKind kind)) := by
  cases kind with
  | uuu => exact h.uuu
  | uut => exact h.uut
  | utu => exact h.uut
  | utt => exact h.utt
  | tuu => exact h.tuu
  | tut => exact h.tut
  | ttu => exact h.tut
  | ttt => exact h.ttt

/-- The six orbit representatives imply the former eight-kind universal
three-row obstruction. -/
theorem SixRepresentativeObstructions.universalThreeRowObstruction
    (h : SixRepresentativeObstructions) : UniversalThreeRowObstruction := by
  intro kind hext
  exact h.refutesRepresentative kind
    (nonempty_threeExtension_representative kind hext)

theorem no_profileB_star_of_sixRepresentativeObstructions
    (h : SixRepresentativeObstructions) :
    ¬Nonempty (CanonicalStarWitness ProfileB) :=
  no_profileB_star_of_universalThreeRowObstruction
    h.universalThreeRowObstruction

#print axioms R4333.ProfileBThreeRowKindSymmetry.transportTailWitness
#print axioms R4333.ProfileBThreeRowKindSymmetry.transportThreeExtension
#print axioms R4333.ProfileBThreeRowKindSymmetry.nonempty_threeExtension_iff_swapKind
#print axioms R4333.ProfileBThreeRowKindSymmetry.SixRepresentativeObstructions.universalThreeRowObstruction
#print axioms R4333.ProfileBThreeRowKindSymmetry.no_profileB_star_of_sixRepresentativeObstructions

end ProfileBThreeRowKindSymmetry
end R4333
