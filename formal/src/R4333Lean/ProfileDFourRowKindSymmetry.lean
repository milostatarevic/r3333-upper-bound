import R4333Lean.ProfileDFourRowBoundary
import R4333Lean.ColorRelabel
import R4333Lean.CriticalTemplatePaletteSymmetry

/-!
# Equal-K15 block symmetry of profile-D four-row extensions

The profile-D tail has block orders `15, 15, 16`.  Interchanging its first
two blocks, together with host colours one and two, preserves the exact
four-row extension problem.  The colour relabelling changes the local
three-colour labels in every block (including the fixed K16), so checked
full-palette automorphisms of the critical templates are applied internally.

This reduces the eight U/T kinds to the six orbits of the transposition of
the first two selector bits.  All transports are semantic; no SAT result is
assumed here.
-/

namespace R4333
namespace ProfileDFourRowKindSymmetry

open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ColoringJoinRows

/-- The only nontrivial block permutation compatible with the unequal
profile-D block orders. -/
def swapFirstTwoBlocks : Equiv.Perm (Fin 3) := Equiv.swap 0 1

@[simp] theorem swapFirstTwoBlocks_zero : swapFirstTwoBlocks 0 = 1 := by
  simp [swapFirstTwoBlocks]

@[simp] theorem swapFirstTwoBlocks_one : swapFirstTwoBlocks 1 = 0 := by
  simp [swapFirstTwoBlocks]

@[simp] theorem swapFirstTwoBlocks_two : swapFirstTwoBlocks 2 = 2 := by
  decide

/-- Swap the first two selector bits and keep the K16 selector fixed. -/
def swapKind (kind : Kind) : Kind :=
  Kind.ofBooleans (kind.twisted 1) (kind.twisted 0) (kind.twisted 2)

@[simp] theorem swapKind_twisted (kind : Kind) (block : Fin 3) :
    (swapKind kind).twisted block =
      kind.twisted (swapFirstTwoBlocks block) := by
  fin_cases block <;>
    simp [swapKind, Kind.twisted_ofBooleans]

@[simp] theorem swapKind_swapKind (kind : Kind) :
    swapKind (swapKind kind) = kind := by
  cases kind <;> rfl

/-- Swap host colours one and two, fixing zero and three.  The orientation
sends the omitted colour of the source block to the omitted colour of the
target block. -/
def hostColorPerm : Equiv.Perm (Fin 4) :=
  (finSuccEquiv 3).trans
    ((Equiv.optionCongr swapFirstTwoBlocks.symm).trans
      (finSuccEquiv 3).symm)

@[simp] theorem hostColorPerm_zero : hostColorPerm 0 = 0 := by rfl

@[simp] theorem hostColorPerm_succ_apply (block : Fin 3) :
    hostColorPerm (Fin.succ (swapFirstTwoBlocks block)) = Fin.succ block := by
  change (finSuccEquiv 3).symm
    (some (swapFirstTwoBlocks.symm (swapFirstTwoBlocks block))) =
      Fin.succ block
  rw [swapFirstTwoBlocks.symm_apply_apply]
  rfl

/-- The canonical palette as an equivalence onto all host colours except
the displayed omitted colour. -/
noncomputable def canonicalPaletteEquiv (block : Fin 4) :
    Fin 3 ≃ {q : Fin 4 // q ≠ block} :=
  Equiv.ofBijective
    (fun q : Fin 3 => ⟨canonicalPalette block q,
      SingleRootStarWitness61.canonicalPalette_ne_block block q⟩)
    (by
      rw [Fintype.bijective_iff_injective_and_card]
      constructor
      · intro left right h
        apply SingleRootStarWitness61.canonicalPalette_injective block
        exact congrArg Subtype.val h
      · simp)

@[simp] theorem canonicalPaletteEquiv_apply_val (block : Fin 4) (q : Fin 3) :
    (canonicalPaletteEquiv block q).val = canonicalPalette block q := rfl

/-- Restrict the host-colour transposition to the corresponding source and
target palettes. -/
def restrictedHostColorPerm (block : Fin 3) :
    {q : Fin 4 // q ≠ Fin.succ (swapFirstTwoBlocks block)} ≃
      {q : Fin 4 // q ≠ Fin.succ block} where
  toFun q := ⟨hostColorPerm q, by
    intro h
    apply q.property
    apply hostColorPerm.injective
    simpa using h⟩
  invFun q := ⟨hostColorPerm.symm q, by
    intro h
    apply q.property
    have := congrArg hostColorPerm h
    simpa using this⟩
  left_inv q := by ext; simp
  right_inv q := by ext; simp

@[simp] theorem restrictedHostColorPerm_apply_val (block : Fin 3)
    (q : {q : Fin 4 // q ≠ Fin.succ (swapFirstTwoBlocks block)}) :
    (restrictedHostColorPerm block q).val = hostColorPerm q.val := rfl

/-- The induced permutation of the three canonical palette labels in one
target block. -/
noncomputable def labelPerm (block : Fin 3) : Equiv.Perm (Fin 3) :=
  (canonicalPaletteEquiv (Fin.succ (swapFirstTwoBlocks block))).trans
    ((restrictedHostColorPerm block).trans
      (canonicalPaletteEquiv (Fin.succ block)).symm)

theorem hostColorPerm_canonicalPalette (block : Fin 3) (q : Fin 3) :
    hostColorPerm
        (canonicalPalette (Fin.succ (swapFirstTwoBlocks block)) q) =
      canonicalPalette (Fin.succ block) (labelPerm block q) := by
  let mid : {q : Fin 4 // q ≠ Fin.succ block} :=
    restrictedHostColorPerm block
      (canonicalPaletteEquiv
        (Fin.succ (swapFirstTwoBlocks block)) q)
  have h := congrArg Subtype.val
    ((canonicalPaletteEquiv (Fin.succ block)).apply_symm_apply mid)
  change canonicalPalette (Fin.succ block)
      ((canonicalPaletteEquiv (Fin.succ block)).symm mid) =
    hostColorPerm
      (canonicalPalette (Fin.succ (swapFirstTwoBlocks block)) q) at h
  change hostColorPerm
      (canonicalPalette (Fin.succ (swapFirstTwoBlocks block)) q) =
    canonicalPalette (Fin.succ block)
      ((canonicalPaletteEquiv (Fin.succ block)).symm mid)
  exact h.symm

/-! ## Checked local palette automorphisms -/

noncomputable def localK15Zero (kind : Kind) : Equiv.Perm (Fin 15) :=
  Classical.choose
    (k15Template_fullPaletteSymmetry (kind.twisted 1) (labelPerm 0).symm)

noncomputable def localK15One (kind : Kind) : Equiv.Perm (Fin 15) :=
  Classical.choose
    (k15Template_fullPaletteSymmetry (kind.twisted 0) (labelPerm 1).symm)

noncomputable def localK16Two (kind : Kind) : Equiv.Perm (Fin 16) :=
  Classical.choose
    (k16Template_fullPaletteSymmetry (kind.twisted 2) (labelPerm 2).symm)

theorem localK15Zero_preserves (kind : Kind) (left right : Fin 15)
    (hlr : left ≠ right) :
    k15Template (kind.twisted 1)
        (localK15Zero kind left) (localK15Zero kind right) =
      (labelPerm 0).symm (k15Template (kind.twisted 1) left right) :=
  (Classical.choose_spec
    (k15Template_fullPaletteSymmetry
      (kind.twisted 1) (labelPerm 0).symm)) left right hlr

theorem localK15One_preserves (kind : Kind) (left right : Fin 15)
    (hlr : left ≠ right) :
    k15Template (kind.twisted 0)
        (localK15One kind left) (localK15One kind right) =
      (labelPerm 1).symm (k15Template (kind.twisted 0) left right) :=
  (Classical.choose_spec
    (k15Template_fullPaletteSymmetry
      (kind.twisted 0) (labelPerm 1).symm)) left right hlr

theorem localK16Two_preserves (kind : Kind) (left right : Fin 16)
    (hlr : left ≠ right) :
    k16Template (kind.twisted 2)
        (localK16Two kind left) (localK16Two kind right) =
      (labelPerm 2).symm (k16Template (kind.twisted 2) left right) :=
  (Classical.choose_spec
    (k16Template_fullPaletteSymmetry
      (kind.twisted 2) (labelPerm 2).symm)) left right hlr

/-! ## Tail vertex transport -/

/-- Decode the contiguous tail as `K15 + K15 + K16`. -/
def tailDecompEquiv : (Fin 15 ⊕ Fin 15) ⊕ Fin 16 ≃ Fin 46 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 16))).trans
    finSumFinEquiv

/-- Swap the two K15 summands and apply the required local automorphism in
all three summands. -/
noncomputable def blockPositionPerm (kind : Kind) :
    Equiv.Perm ((Fin 15 ⊕ Fin 15) ⊕ Fin 16) where
  toFun
    | .inl (.inl x) => .inl (.inr (localK15Zero kind x))
    | .inl (.inr x) => .inl (.inl (localK15One kind x))
    | .inr x => .inr (localK16Two kind x)
  invFun
    | .inl (.inl x) => .inl (.inr ((localK15One kind).symm x))
    | .inl (.inr x) => .inl (.inl ((localK15Zero kind).symm x))
    | .inr x => .inr ((localK16Two kind).symm x)
  left_inv x := by
    rcases x with (⟨⟨x⟩⟩ | ⟨⟨x⟩⟩ | ⟨x⟩) <;> simp
  right_inv x := by
    rcases x with (⟨⟨x⟩⟩ | ⟨⟨x⟩⟩ | ⟨x⟩) <;> simp

/-- The resulting permutation of the contiguous 46-vertex tail. -/
noncomputable def tailVertexPerm (kind : Kind) : Equiv.Perm (Fin 46) :=
  tailDecompEquiv.symm.trans ((blockPositionPerm kind).trans tailDecompEquiv)

theorem tailDecompEquiv_blockZero (position : Fin 15) :
    tailDecompEquiv (.inl (.inl position)) =
      blockVertex 0 position.val := by
  apply Fin.ext
  rw [blockVertex_val 0 (by
    simp [ProfileDTripleJoinReduction.blockSize])]
  change (finSumFinEquiv
    (Sum.inl (finSumFinEquiv (Sum.inl position)))).val = _
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
  simp [ProfileDTripleJoinReduction.blockStart]

theorem tailDecompEquiv_blockOne (position : Fin 15) :
    tailDecompEquiv (.inl (.inr position)) =
      blockVertex 1 position.val := by
  apply Fin.ext
  rw [blockVertex_val 1 (by
    simp [ProfileDTripleJoinReduction.blockSize])]
  change (finSumFinEquiv
    (Sum.inl (finSumFinEquiv (Sum.inr position)))).val = _
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  rfl

theorem tailDecompEquiv_blockTwo (position : Fin 16) :
    tailDecompEquiv (.inr position) =
      blockVertex 2 position.val := by
  apply Fin.ext
  rw [blockVertex_val 2 (by
    simp [ProfileDTripleJoinReduction.blockSize])]
  change (finSumFinEquiv (Sum.inr position)).val = _
  rw [finSumFinEquiv_apply_right]
  rfl

theorem tailVertexPerm_blockZero (kind : Kind) (position : Fin 15) :
    tailVertexPerm kind (blockVertex 0 position.val) =
      blockVertex 1 (localK15Zero kind position).val := by
  rw [← tailDecompEquiv_blockZero position]
  simp only [tailVertexPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  change tailDecompEquiv
      (blockPositionPerm kind (.inl (.inl position))) = _
  exact tailDecompEquiv_blockOne (localK15Zero kind position)

theorem tailVertexPerm_blockOne (kind : Kind) (position : Fin 15) :
    tailVertexPerm kind (blockVertex 1 position.val) =
      blockVertex 0 (localK15One kind position).val := by
  rw [← tailDecompEquiv_blockOne position]
  simp only [tailVertexPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  change tailDecompEquiv
      (blockPositionPerm kind (.inl (.inr position))) = _
  exact tailDecompEquiv_blockZero (localK15One kind position)

theorem tailVertexPerm_blockTwo (kind : Kind) (position : Fin 16) :
    tailVertexPerm kind (blockVertex 2 position.val) =
      blockVertex 2 (localK16Two kind position).val := by
  rw [← tailDecompEquiv_blockTwo position]
  simp only [tailVertexPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  change tailDecompEquiv (blockPositionPerm kind (.inr position)) = _
  exact tailDecompEquiv_blockTwo (localK16Two kind position)

/-! ## Semantic witness and four-row transport -/

/-- Extend the ordered-pair template field of a witness to arbitrary
distinct K15 coordinates in either of its first two blocks. -/
theorem witness_internal_eq_canonicalK15 {kind : Kind} (tail : Witness kind)
    (block : Fin 3) (hsize : blockSize block = 15)
    (left right : Fin 15) (hlr : left ≠ right) :
    tail.coloring (blockVertex block left.val) (blockVertex block right.val) =
      canonicalPalette (Fin.succ block)
        (k15Template (kind.twisted block) left right) := by
  have hval : left.val ≠ right.val := fun h => hlr (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hcanonical := tail.templateCanonical block left.val right.val
      (by simp [hsize])
      (by simp [hsize]) hlt
    simpa [hsize, templateColor, fin15,
      Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt]
      using hcanonical
  · have hcanonical := tail.templateCanonical block right.val left.val
      (by simp [hsize])
      (by simp [hsize]) hgt
    rw [tail.coloring.color_symm,
      (k15Template (kind.twisted block)).color_symm]
    simpa [hsize, templateColor, fin15,
      Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt]
      using hcanonical

/-- The analogous unordered form for the fixed K16 block. -/
theorem witness_internal_eq_canonicalK16 {kind : Kind} (tail : Witness kind)
    (block : Fin 3) (hsize : blockSize block = 16)
    (left right : Fin 16) (hlr : left ≠ right) :
    tail.coloring (blockVertex block left.val) (blockVertex block right.val) =
      canonicalPalette (Fin.succ block)
        (k16Template (kind.twisted block) left right) := by
  have hval : left.val ≠ right.val := fun h => hlr (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hcanonical := tail.templateCanonical block left.val right.val
      (by simp [hsize])
      (by simp [hsize]) hlt
    simpa [hsize, templateColor, fin16,
      Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt]
      using hcanonical
  · have hcanonical := tail.templateCanonical block right.val left.val
      (by simp [hsize])
      (by simp [hsize]) hgt
    rw [tail.coloring.color_symm,
      (k16Template (kind.twisted block)).color_symm]
    simpa [hsize, templateColor, fin16,
      Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt]
      using hcanonical

/-- Transport an exact profile-D tail witness across the equal-K15 block
transposition. -/
noncomputable def transportWitness {kind : Kind} (tail : Witness kind) :
    Witness (swapKind kind) where
  coloring := mapEdgeColors
    (relabelVertices tail.coloring (tailVertexPerm kind)) hostColorPerm
  noMono := noMono_mapEdgeColors _ _
    (noMono_relabelVertices _ _ tail.noMono)
  templateCanonical := by
    intro block left right hleft hright hlr
    fin_cases block
    · simp only [swapKind_twisted,
        ProfileDTripleJoinReduction.blockSize] at hleft hright ⊢
      let leftFin : Fin 15 := ⟨left, by
        simpa [ProfileDTripleJoinReduction.blockSize] using hleft⟩
      let rightFin : Fin 15 := ⟨right, by
        simpa [ProfileDTripleJoinReduction.blockSize] using hright⟩
      have hfinNe : leftFin ≠ rightFin :=
        Fin.ne_of_lt (by simpa [leftFin, rightFin] using hlr)
      have hmapNe : localK15Zero kind leftFin ≠
          localK15Zero kind rightFin :=
        (localK15Zero kind).injective.ne hfinNe
      rw [mapEdgeColors_apply, relabelVertices_apply]
      change hostColorPerm
          (tail.coloring
            (tailVertexPerm kind (blockVertex 0 leftFin.val))
            (tailVertexPerm kind (blockVertex 0 rightFin.val))) =
        canonicalPalette 1
          (templateColor 15 (kind.twisted 1) leftFin.val rightFin.val)
      rw [
        tailVertexPerm_blockZero kind leftFin,
        tailVertexPerm_blockZero kind rightFin]
      rw [witness_internal_eq_canonicalK15 tail 1
        (by simp [ProfileDTripleJoinReduction.blockSize]) _ _ hmapNe]
      change hostColorPerm
          (canonicalPalette 2
            (k15Template (kind.twisted 1)
              (localK15Zero kind leftFin)
              (localK15Zero kind rightFin))) =
        canonicalPalette 1
          (templateColor 15 (kind.twisted 1) left right)
      rw [localK15Zero_preserves kind leftFin rightFin hfinNe]
      rw [show hostColorPerm
          (canonicalPalette 2
            ((labelPerm 0).symm
              (k15Template (kind.twisted 1) leftFin rightFin))) =
          canonicalPalette 1
            (labelPerm 0 ((labelPerm 0).symm
              (k15Template (kind.twisted 1) leftFin rightFin))) by
        simpa using hostColorPerm_canonicalPalette (0 : Fin 3)
          ((labelPerm 0).symm
            (k15Template (kind.twisted 1) leftFin rightFin))]
      simp [templateColor, fin15, leftFin, rightFin,
        Nat.mod_eq_of_lt leftFin.isLt, Nat.mod_eq_of_lt rightFin.isLt]
    · simp only [swapKind_twisted,
        ProfileDTripleJoinReduction.blockSize] at hleft hright ⊢
      let leftFin : Fin 15 := ⟨left, by
        simpa [ProfileDTripleJoinReduction.blockSize] using hleft⟩
      let rightFin : Fin 15 := ⟨right, by
        simpa [ProfileDTripleJoinReduction.blockSize] using hright⟩
      have hfinNe : leftFin ≠ rightFin :=
        Fin.ne_of_lt (by simpa [leftFin, rightFin] using hlr)
      have hmapNe : localK15One kind leftFin ≠
          localK15One kind rightFin :=
        (localK15One kind).injective.ne hfinNe
      rw [mapEdgeColors_apply, relabelVertices_apply]
      change hostColorPerm
          (tail.coloring
            (tailVertexPerm kind (blockVertex 1 leftFin.val))
            (tailVertexPerm kind (blockVertex 1 rightFin.val))) =
        canonicalPalette 2
          (templateColor 15 (kind.twisted 0) leftFin.val rightFin.val)
      rw [
        tailVertexPerm_blockOne kind leftFin,
        tailVertexPerm_blockOne kind rightFin]
      rw [witness_internal_eq_canonicalK15 tail 0
        (by simp [ProfileDTripleJoinReduction.blockSize]) _ _ hmapNe]
      change hostColorPerm
          (canonicalPalette 1
            (k15Template (kind.twisted 0)
              (localK15One kind leftFin)
              (localK15One kind rightFin))) =
        canonicalPalette 2
          (templateColor 15 (kind.twisted 0) left right)
      rw [localK15One_preserves kind leftFin rightFin hfinNe]
      rw [show hostColorPerm
          (canonicalPalette 1
            ((labelPerm 1).symm
              (k15Template (kind.twisted 0) leftFin rightFin))) =
          canonicalPalette 2
            (labelPerm 1 ((labelPerm 1).symm
              (k15Template (kind.twisted 0) leftFin rightFin))) by
        simpa using hostColorPerm_canonicalPalette (1 : Fin 3)
          ((labelPerm 1).symm
            (k15Template (kind.twisted 0) leftFin rightFin))]
      simp [templateColor, fin15, leftFin, rightFin,
        Nat.mod_eq_of_lt leftFin.isLt, Nat.mod_eq_of_lt rightFin.isLt]
    · simp only [swapKind_twisted,
        ProfileDTripleJoinReduction.blockSize] at hleft hright ⊢
      let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileDTripleJoinReduction.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileDTripleJoinReduction.blockSize] using hright⟩
      have hfinNe : leftFin ≠ rightFin :=
        Fin.ne_of_lt (by simpa [leftFin, rightFin] using hlr)
      have hmapNe : localK16Two kind leftFin ≠
          localK16Two kind rightFin :=
        (localK16Two kind).injective.ne hfinNe
      rw [mapEdgeColors_apply, relabelVertices_apply]
      change hostColorPerm
          (tail.coloring
            (tailVertexPerm kind (blockVertex 2 leftFin.val))
            (tailVertexPerm kind (blockVertex 2 rightFin.val))) =
        canonicalPalette 3
          (templateColor 16 (kind.twisted 2) leftFin.val rightFin.val)
      rw [
        tailVertexPerm_blockTwo kind leftFin,
        tailVertexPerm_blockTwo kind rightFin]
      rw [witness_internal_eq_canonicalK16 tail 2
        (by simp [ProfileDTripleJoinReduction.blockSize]) _ _ hmapNe]
      change hostColorPerm
          (canonicalPalette 3
            (k16Template (kind.twisted 2)
              (localK16Two kind leftFin)
              (localK16Two kind rightFin))) =
        canonicalPalette 3
          (templateColor 16 (kind.twisted 2) left right)
      rw [localK16Two_preserves kind leftFin rightFin hfinNe]
      rw [show hostColorPerm
          (canonicalPalette 3
            ((labelPerm 2).symm
              (k16Template (kind.twisted 2) leftFin rightFin))) =
          canonicalPalette 3
            (labelPerm 2 ((labelPerm 2).symm
              (k16Template (kind.twisted 2) leftFin rightFin))) by
        simpa using hostColorPerm_canonicalPalette (2 : Fin 3)
          ((labelPerm 2).symm
            (k16Template (kind.twisted 2) leftFin rightFin))]
      simp [templateColor, fin16, leftFin, rightFin,
        Nat.mod_eq_of_lt leftFin.isLt, Nat.mod_eq_of_lt rightFin.isLt]

/-- Transport the full exact four-row object.  The four free vertices stay
fixed while all tail vertices and host colours are relabelled. -/
noncomputable def transportFourExtension {kind : Kind}
    (ext : FourExtension kind) : FourExtension (swapKind kind) where
  tail := transportWitness ext.tail
  inside := mapEdgeColors ext.inside hostColorPerm
  rows := fun a x => hostColorPerm (ext.rows a (tailVertexPerm kind x))
  insideNoMono := noMono_mapEdgeColors _ _ ext.insideNoMono
  insideRootForbidden := by
    intro a b hab hzero
    apply ext.insideRootForbidden a b hab
    apply hostColorPerm.injective
    simpa using hzero
  rowsAdmissible := by
    intro a x y hxy hbad
    apply ext.rowsAdmissible a
      (tailVertexPerm kind x) (tailVertexPerm kind y)
      ((tailVertexPerm kind).injective.ne hxy)
    exact ⟨hostColorPerm.injective hbad.1,
      hostColorPerm.injective hbad.2⟩
  rowsPairCompatible := by
    intro a b hab x hbad
    apply ext.rowsPairCompatible a b hab (tailVertexPerm kind x)
    exact ⟨hostColorPerm.injective hbad.1,
      hostColorPerm.injective hbad.2⟩

theorem nonempty_transportFourExtension {kind : Kind} :
    Nonempty (FourExtension kind) →
      Nonempty (FourExtension (swapKind kind)) := by
  rintro ⟨ext⟩
  exact ⟨transportFourExtension ext⟩

/-- The transposition is an equivalence on extension-existence
propositions. -/
theorem nonempty_fourExtension_iff_swapKind (kind : Kind) :
    Nonempty (FourExtension kind) ↔
      Nonempty (FourExtension (swapKind kind)) := by
  constructor
  · exact nonempty_transportFourExtension
  · intro h
    have hback := nonempty_transportFourExtension h
    simpa using hback

/-! ## Six orbit representatives -/

/-- The six kinds representing the orbits under swapping the K15 blocks. -/
structure SwapRepresentativeObstructions : Prop where
  uuu : ¬Nonempty (FourExtension .uuu)
  uut : ¬Nonempty (FourExtension .uut)
  utu : ¬Nonempty (FourExtension .utu)
  utt : ¬Nonempty (FourExtension .utt)
  ttu : ¬Nonempty (FourExtension .ttu)
  ttt : ¬Nonempty (FourExtension .ttt)

/-- Six representative obstructions imply the former eight-kind universal
profile-D four-row obstruction. -/
theorem SwapRepresentativeObstructions.universalFourRowObstruction
    (h : SwapRepresentativeObstructions) : UniversalFourRowObstruction := by
  intro kind
  cases kind with
  | uuu => exact h.uuu
  | uut => exact h.uut
  | utu => exact h.utu
  | utt => exact h.utt
  | tuu =>
      intro hext
      apply h.utu
      have htransported := nonempty_transportFourExtension hext
      simpa [swapKind, Kind.twisted, Kind.ofBooleans] using htransported
  | tut =>
      intro hext
      apply h.utt
      have htransported := nonempty_transportFourExtension hext
      simpa [swapKind, Kind.twisted, Kind.ofBooleans] using htransported
  | ttu => exact h.ttu
  | ttt => exact h.ttt

/-- Hence the six orbit representatives eliminate the full profile-D
single-root branch. -/
theorem no_profileD_star_of_swapRepresentativeObstructions
    (h : SwapRepresentativeObstructions) :
    ¬Nonempty (CanonicalStarWitness ProfileD) :=
  no_profileD_star_of_universalFourRowObstruction
    h.universalFourRowObstruction

#print axioms R4333.ProfileDFourRowKindSymmetry.transportWitness
#print axioms R4333.ProfileDFourRowKindSymmetry.transportFourExtension
#print axioms R4333.ProfileDFourRowKindSymmetry.nonempty_fourExtension_iff_swapKind
#print axioms R4333.ProfileDFourRowKindSymmetry.SwapRepresentativeObstructions.universalFourRowObstruction
#print axioms R4333.ProfileDFourRowKindSymmetry.no_profileD_star_of_swapRepresentativeObstructions

end ProfileDFourRowKindSymmetry
end R4333
