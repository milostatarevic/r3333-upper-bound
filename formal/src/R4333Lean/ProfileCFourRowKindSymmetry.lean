import R4333Lean.ProfileBCFourRowBoundary
import R4333Lean.ColorRelabel
import R4333Lean.CriticalTemplatePaletteSymmetry

/-!
# Symmetry of the profile-C four-row template kinds

The noncritical `K14` tail block is kept pointwise fixed.  The two critical
`K16` tail blocks may be interchanged, provided host colours two and three
are interchanged and each canonical `K16` is internally relabelled by the
checked palette automorphism induced by that host-colour swap.  Thus the
mixed kinds `ut` and `tu` are semantically equivalent, and only the three
representatives `uu`, `ut`, and `tt` need independent refutations.

All transports in this file are semantic.  The arbitrary colouring on the
noncritical `K14`, including its colour-one root-forbidden law, is preserved
rather than normalized.
-/

namespace R4333
namespace ProfileCFourRowKindSymmetry

open SingleRootStarCNF
open ColoringJoinRows
open ProfileCRowExtension
open ProfileCFourRowBoundary

/-! ## The block, kind, and host-colour permutations -/

/-- Fix the noncritical block zero and interchange critical blocks one and
two. -/
noncomputable def blockSwap : Equiv.Perm (Fin 3) :=
  criticalPaletteColorEquiv 1

@[simp] theorem blockSwap_zero : blockSwap 0 = 0 := by
  rfl

@[simp] theorem blockSwap_one : blockSwap 1 = 2 := by
  rfl

@[simp] theorem blockSwap_two : blockSwap 2 = 1 := by
  rfl

@[simp] theorem blockSwap_involutive (block : Fin 3) :
    blockSwap (blockSwap block) = block := by
  fin_cases block <;> rfl

/-- Interchange the two genuine profile-C template selector bits. -/
def swapKind (kind : Kind) : Kind :=
  Kind.ofBooleans (kind.twisted 2) (kind.twisted 1)

@[simp] theorem swapKind_twisted (kind : Kind) (block : Fin 3) :
    (swapKind kind).twisted block = kind.twisted (blockSwap block) := by
  cases kind <;> fin_cases block <;> rfl

@[simp] theorem swapKind_involutive (kind : Kind) :
    swapKind (swapKind kind) = kind := by
  cases kind <;> rfl

@[simp] theorem swapKind_tu : swapKind .tu = .ut := by
  rfl

/-- Extend `blockSwap` to four host colours, fixing root colour zero.  The
orientation sends the omitted colour of the source block `blockSwap block`
to the omitted colour of target block `block`. -/
noncomputable def hostColorSwap : Equiv.Perm (Fin 4) :=
  (finSuccEquiv 3).trans
    ((Equiv.optionCongr blockSwap.symm).trans (finSuccEquiv 3).symm)

@[simp] theorem hostColorSwap_zero : hostColorSwap 0 = 0 := by
  rfl

@[simp] theorem hostColorSwap_succ (block : Fin 3) :
    hostColorSwap (Fin.succ (blockSwap block)) = Fin.succ block := by
  change (finSuccEquiv 3).symm
    (some (blockSwap.symm (blockSwap block))) = Fin.succ block
  rw [blockSwap.symm_apply_apply]
  rfl

@[simp] theorem hostColorSwap_one : hostColorSwap 1 = 1 := by
  simpa using hostColorSwap_succ (0 : Fin 3)

/-! ## Palette transport inside the two critical K16s -/

/-- The canonical palette as an equivalence onto all host colours except
the omitted block colour. -/
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

/-- Restrict the global host-colour swap between the source and target
three-colour palettes of a tail block. -/
noncomputable def restrictedHostColorSwap (block : Fin 3) :
    {q : Fin 4 // q ≠ Fin.succ (blockSwap block)} ≃
      {q : Fin 4 // q ≠ Fin.succ block} where
  toFun q := ⟨hostColorSwap q, by
    intro h
    apply q.property
    apply hostColorSwap.injective
    simpa using h⟩
  invFun q := ⟨hostColorSwap.symm q, by
    intro h
    apply q.property
    have := congrArg hostColorSwap h
    simpa using this⟩
  left_inv q := by ext; simp
  right_inv q := by ext; simp

/-- Palette-label permutation induced by the block and host-colour swap. -/
noncomputable def labelPerm (block : Fin 3) : Equiv.Perm (Fin 3) :=
  (canonicalPaletteEquiv (Fin.succ (blockSwap block))).trans
    ((restrictedHostColorSwap block).trans
      (canonicalPaletteEquiv (Fin.succ block)).symm)

theorem hostColorSwap_canonicalPalette (block : Fin 3) (q : Fin 3) :
    hostColorSwap
        (canonicalPalette (Fin.succ (blockSwap block)) q) =
      canonicalPalette (Fin.succ block) (labelPerm block q) := by
  let mid : {q : Fin 4 // q ≠ Fin.succ block} :=
    restrictedHostColorSwap block
      (canonicalPaletteEquiv (Fin.succ (blockSwap block)) q)
  have h := congrArg Subtype.val
    ((canonicalPaletteEquiv (Fin.succ block)).apply_symm_apply mid)
  change canonicalPalette (Fin.succ block)
      ((canonicalPaletteEquiv (Fin.succ block)).symm mid) =
    hostColorSwap
      (canonicalPalette (Fin.succ (blockSwap block)) q) at h
  change hostColorSwap
      (canonicalPalette (Fin.succ (blockSwap block)) q) =
    canonicalPalette (Fin.succ block)
      ((canonicalPaletteEquiv (Fin.succ block)).symm mid)
  exact h.symm

/-- Internal vertex relabelling of the source K16 that compensates for the
induced permutation of its three canonical palette labels. -/
noncomputable def localVertexPerm (kind : Kind) (block : Fin 3) :
    Equiv.Perm (Fin 16) :=
  Classical.choose
    (k16Template_fullPaletteSymmetry
      (kind.twisted (blockSwap block)) (labelPerm block).symm)

theorem localVertexPerm_preserves (kind : Kind) (block : Fin 3)
    (left right : Fin 16) (hlr : left ≠ right) :
    k16Template (kind.twisted (blockSwap block))
        (localVertexPerm kind block left)
        (localVertexPerm kind block right) =
      (labelPerm block).symm
        (k16Template (kind.twisted (blockSwap block)) left right) :=
  (Classical.choose_spec
    (k16Template_fullPaletteSymmetry
      (kind.twisted (blockSwap block)) (labelPerm block).symm))
    left right hlr

/-! ## A permutation of the contiguous `K14 + K16 + K16` tail -/

/-- Interchange the two coordinates indexing the critical K16 blocks. -/
noncomputable def criticalIndexSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

@[simp] theorem criticalIndexSwap_zero : criticalIndexSwap 0 = 1 := by
  simp [criticalIndexSwap]

@[simp] theorem criticalIndexSwap_one : criticalIndexSwap 1 = 0 := by
  simp [criticalIndexSwap]

@[simp] theorem succ_criticalIndexSwap (index : Fin 2) :
    Fin.succ (criticalIndexSwap index) = blockSwap (Fin.succ index) := by
  fin_cases index <;> rfl

/-- On a target critical block-position pair, jump to the corresponding
source block and apply its required internal palette automorphism. -/
noncomputable def criticalPositionPerm (kind : Kind) :
    Equiv.Perm (Fin 2 × Fin 16) where
  toFun pair :=
    (criticalIndexSwap pair.1,
      localVertexPerm kind (Fin.succ pair.1) pair.2)
  invFun pair :=
    (criticalIndexSwap.symm pair.1,
      (localVertexPerm kind (Fin.succ (criticalIndexSwap.symm pair.1))).symm
        pair.2)
  left_inv pair := by
    rcases pair with ⟨index, position⟩
    simp
  right_inv pair := by
    rcases pair with ⟨index, position⟩
    simp

abbrev SplitTail := Fin 14 ⊕ (Fin 2 × Fin 16)

/-- The standard contiguous encoding of the fixed K14 followed by two
K16 fibres. -/
noncomputable def splitTailEquiv : SplitTail ≃ TailVertex :=
  (Equiv.sumCongr (Equiv.refl (Fin 14)) finProdFinEquiv).trans
    finSumFinEquiv

/-- Fix the K14 coordinates and apply `criticalPositionPerm` to the final
32 coordinates. -/
noncomputable def splitTailPerm (kind : Kind) : Equiv.Perm SplitTail :=
  Equiv.sumCongr (Equiv.refl (Fin 14)) (criticalPositionPerm kind)

/-- The resulting permutation of the contiguous 46-vertex tail.  Its input
is a target coordinate and its output is the corresponding source
coordinate, as required by `relabelVertices`. -/
noncomputable def tailVertexPerm (kind : Kind) : Equiv.Perm TailVertex :=
  splitTailEquiv.symm.trans ((splitTailPerm kind).trans splitTailEquiv)

theorem splitTailEquiv_noncritical (position : Fin 14) :
    splitTailEquiv (Sum.inl position) =
      blockVertex 0 position.val := by
  apply Fin.ext
  rw [ProfileCRowExtension.blockVertex_val 0 (by
    simp [ProfileCRowExtension.blockSize])]
  simp only [splitTailEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.refl_apply]
  rw [show ProfileCRowExtension.blockStart (0 : Fin 3) = 0 by decide]
  change position.val = 0 + position.val
  omega

theorem blockStart_critical (index : Fin 2) :
    ProfileCRowExtension.blockStart (Fin.succ index) =
      14 + 16 * index.val := by
  fin_cases index <;> decide

theorem splitTailEquiv_critical (index : Fin 2) (position : Fin 16) :
    splitTailEquiv (Sum.inr (index, position)) =
      blockVertex (Fin.succ index) position.val := by
  apply Fin.ext
  rw [ProfileCRowExtension.blockVertex_val (Fin.succ index) (by
    fin_cases index <;>
      simp [ProfileCRowExtension.blockSize])]
  simp only [splitTailEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inr]
  rw [blockStart_critical]
  change 14 + (position.val + 16 * index.val) =
    14 + 16 * index.val + position.val
  omega

theorem tailVertexPerm_noncritical (kind : Kind) (position : Fin 14) :
    tailVertexPerm kind (blockVertex 0 position.val) =
      blockVertex 0 position.val := by
  rw [← splitTailEquiv_noncritical position]
  simp [tailVertexPerm, splitTailPerm]

theorem tailVertexPerm_critical (kind : Kind) (index : Fin 2)
    (position : Fin 16) :
    tailVertexPerm kind (blockVertex (Fin.succ index) position.val) =
      blockVertex (Fin.succ (criticalIndexSwap index))
        (localVertexPerm kind (Fin.succ index) position).val := by
  rw [← splitTailEquiv_critical index position]
  simp only [tailVertexPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  change splitTailEquiv
      (splitTailPerm kind (Sum.inr (index, position))) = _
  change splitTailEquiv
      (Sum.inr (criticalIndexSwap index,
        localVertexPerm kind (Fin.succ index) position)) = _
  exact splitTailEquiv_critical _ _

theorem tailVertexPerm_blockOne (kind : Kind) (position : Fin 16) :
    tailVertexPerm kind (blockVertex 1 position.val) =
      blockVertex 2 (localVertexPerm kind 1 position).val := by
  simpa using tailVertexPerm_critical kind (0 : Fin 2) position

theorem tailVertexPerm_blockTwo (kind : Kind) (position : Fin 16) :
    tailVertexPerm kind (blockVertex 2 position.val) =
      blockVertex 1 (localVertexPerm kind 2 position).val := by
  simpa using tailVertexPerm_critical kind (1 : Fin 2) position

/-! ## Transport of exact tail witnesses -/

/-- Extend the ordered-pair K16 template field to arbitrary distinct local
coordinates in a critical block. -/
theorem tailWitness_internal_eq_canonicalK16 {kind : Kind}
    (tail : TailWitness kind) (block : Fin 3)
    (hcritical : isCriticalBlock ProfileC (Fin.succ block))
    (left right : Fin 16) (hlr : left ≠ right) :
    tail.coloring (blockVertex block left.val) (blockVertex block right.val) =
      canonicalPalette (Fin.succ block)
        (k16Template (kind.twisted block) left right) := by
  have hsize : ProfileCRowExtension.blockSize block = 16 := by
    fin_cases block
    · simp [isCriticalBlock, SingleRootStarCNF.blockSize, profileSizes]
        at hcritical
    · rfl
    · rfl
  have hval : left.val ≠ right.val := fun h ↦ hlr (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hcanonical := tail.templateCanonical block hcritical
      left.val right.val
      (by simp [hsize])
      (by simp [hsize]) hlt
    simpa [templateColor, hsize, fin16, Nat.mod_eq_of_lt left.isLt,
      Nat.mod_eq_of_lt right.isLt] using hcanonical
  · have hcanonical := tail.templateCanonical block hcritical
      right.val left.val
      (by simp [hsize])
      (by simp [hsize]) hgt
    rw [tail.coloring.color_symm]
    rw [show k16Template (kind.twisted block) left right =
        k16Template (kind.twisted block) right left by
      exact (k16Template (kind.twisted block)).color_symm left right]
    simpa [templateColor, hsize, fin16, Nat.mod_eq_of_lt left.isLt,
      Nat.mod_eq_of_lt right.isLt] using hcanonical

/-- The root-forbidden field, extended from ordered natural coordinates to
arbitrary distinct coordinates with the same block bounds. -/
theorem tailWitness_rootForbidden_of_ne {kind : Kind}
    (tail : TailWitness kind) (block : Fin 3)
    (left right : Nat)
    (hleft : left < ProfileCRowExtension.blockSize block)
    (hright : right < ProfileCRowExtension.blockSize block)
    (hlr : left ≠ right) :
    tail.coloring (blockVertex block left) (blockVertex block right) ≠
      Fin.succ block := by
  rcases lt_or_gt_of_ne hlr with hlt | hgt
  · exact tail.rootForbidden block left right hleft hright hlt
  · intro hbad
    apply tail.rootForbidden block right left hright hleft hgt
    rw [tail.coloring.color_symm]
    exact hbad

/-- Transport an exact profile-C tail witness by fixing the arbitrary K14
and interchanging the two canonical K16 blocks. -/
noncomputable def transportTailWitness {kind : Kind}
    (tail : TailWitness kind) : TailWitness (swapKind kind) where
  coloring := mapEdgeColors
    (relabelVertices tail.coloring (tailVertexPerm kind)) hostColorSwap
  noMono := noMono_mapEdgeColors _ _
    (noMono_relabelVertices _ _ tail.noMono)
  rootForbidden := by
    intro block left right hleft hright hlr
    fin_cases block
    · change hostColorSwap
          (tail.coloring
            (tailVertexPerm kind (blockVertex 0 left))
            (tailVertexPerm kind (blockVertex 0 right))) ≠ 1
      let leftFin : Fin 14 := ⟨left, by
        simpa [ProfileCRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 14 := ⟨right, by
        simpa [ProfileCRowExtension.blockSize] using hright⟩
      rw [tailVertexPerm_noncritical kind leftFin,
        tailVertexPerm_noncritical kind rightFin]
      intro hbad
      apply tail.rootForbidden 0 left right
        (by simpa [ProfileCRowExtension.blockSize] using hleft)
        (by simpa [ProfileCRowExtension.blockSize] using hright) hlr
      apply hostColorSwap.injective
      simpa using hbad
    · change hostColorSwap
          (tail.coloring
            (tailVertexPerm kind (blockVertex 1 left))
            (tailVertexPerm kind (blockVertex 1 right))) ≠ 2
      let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileCRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileCRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := by
        apply Fin.ne_of_lt
        simpa [leftFin, rightFin] using hlr
      rw [tailVertexPerm_blockOne kind leftFin,
        tailVertexPerm_blockOne kind rightFin]
      intro hbad
      have hmapValNe :
          (localVertexPerm kind 1 leftFin).val ≠
            (localVertexPerm kind 1 rightFin).val := fun hval ↦
        (localVertexPerm kind 1).injective.ne hne (Fin.ext hval)
      apply tailWitness_rootForbidden_of_ne tail 2
        (localVertexPerm kind 1 leftFin).val
        (localVertexPerm kind 1 rightFin).val
        (by simp [ProfileCRowExtension.blockSize])
        (by simp [ProfileCRowExtension.blockSize])
        hmapValNe
      have homitted : hostColorSwap (3 : Fin 4) = 2 := by
        simpa using hostColorSwap_succ (1 : Fin 3)
      exact hostColorSwap.injective (hbad.trans homitted.symm)
    · change hostColorSwap
          (tail.coloring
            (tailVertexPerm kind (blockVertex 2 left))
            (tailVertexPerm kind (blockVertex 2 right))) ≠ 3
      let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileCRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileCRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := by
        apply Fin.ne_of_lt
        simpa [leftFin, rightFin] using hlr
      rw [tailVertexPerm_blockTwo kind leftFin,
        tailVertexPerm_blockTwo kind rightFin]
      intro hbad
      have hmapValNe :
          (localVertexPerm kind 2 leftFin).val ≠
            (localVertexPerm kind 2 rightFin).val := fun hval ↦
        (localVertexPerm kind 2).injective.ne hne (Fin.ext hval)
      apply tailWitness_rootForbidden_of_ne tail 1
        (localVertexPerm kind 2 leftFin).val
        (localVertexPerm kind 2 rightFin).val
        (by simp [ProfileCRowExtension.blockSize])
        (by simp [ProfileCRowExtension.blockSize])
        hmapValNe
      have homitted : hostColorSwap (2 : Fin 4) = 3 := by
        simpa using hostColorSwap_succ (2 : Fin 3)
      exact hostColorSwap.injective (hbad.trans homitted.symm)
  templateCanonical := by
    intro block hcritical left right hleft hright hlr
    fin_cases block
    · simp [isCriticalBlock, SingleRootStarCNF.blockSize, profileSizes]
        at hcritical
    · change hostColorSwap
          (tail.coloring
            (tailVertexPerm kind (blockVertex 1 left))
            (tailVertexPerm kind (blockVertex 1 right))) =
          canonicalPalette 2
            (templateColor 16 ((swapKind kind).twisted 1) left right)
      let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileCRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileCRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := by
        apply Fin.ne_of_lt
        simpa [leftFin, rightFin] using hlr
      have hmapNe : localVertexPerm kind 1 leftFin ≠
          localVertexPerm kind 1 rightFin :=
        (localVertexPerm kind 1).injective.ne hne
      rw [tailVertexPerm_blockOne kind leftFin,
        tailVertexPerm_blockOne kind rightFin]
      rw [tailWitness_internal_eq_canonicalK16 tail 2 (by decide)
        (localVertexPerm kind 1 leftFin)
        (localVertexPerm kind 1 rightFin) hmapNe]
      rw [swapKind_twisted]
      simp only [blockSwap_one]
      change hostColorSwap
          (canonicalPalette 3
            (k16Template (kind.twisted 2)
              (localVertexPerm kind 1 leftFin)
              (localVertexPerm kind 1 rightFin))) = _
      have hpreserves :=
        localVertexPerm_preserves kind 1 leftFin rightFin hne
      simp only [blockSwap_one] at hpreserves
      rw [hpreserves]
      have hpalette := hostColorSwap_canonicalPalette (1 : Fin 3)
        ((labelPerm 1).symm
          (k16Template (kind.twisted 2) leftFin rightFin))
      simp only [blockSwap_one] at hpalette
      have hpalette' :
          hostColorSwap
              (canonicalPalette 3
                ((labelPerm 1).symm
                  (k16Template (kind.twisted 2) leftFin rightFin))) =
            canonicalPalette 2
              (labelPerm 1
                ((labelPerm 1).symm
                  (k16Template (kind.twisted 2) leftFin rightFin))) := by
        simpa using hpalette
      rw [hpalette']
      have hleftFin16 : fin16 left = leftFin := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt leftFin.isLt
      have hrightFin16 : fin16 right = rightFin := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt rightFin.isLt
      simp [templateColor, hleftFin16, hrightFin16]
    · change hostColorSwap
          (tail.coloring
            (tailVertexPerm kind (blockVertex 2 left))
            (tailVertexPerm kind (blockVertex 2 right))) =
          canonicalPalette 3
            (templateColor 16 ((swapKind kind).twisted 2) left right)
      let leftFin : Fin 16 := ⟨left, by
        simpa [ProfileCRowExtension.blockSize] using hleft⟩
      let rightFin : Fin 16 := ⟨right, by
        simpa [ProfileCRowExtension.blockSize] using hright⟩
      have hne : leftFin ≠ rightFin := by
        apply Fin.ne_of_lt
        simpa [leftFin, rightFin] using hlr
      have hmapNe : localVertexPerm kind 2 leftFin ≠
          localVertexPerm kind 2 rightFin :=
        (localVertexPerm kind 2).injective.ne hne
      rw [tailVertexPerm_blockTwo kind leftFin,
        tailVertexPerm_blockTwo kind rightFin]
      rw [tailWitness_internal_eq_canonicalK16 tail 1 (by decide)
        (localVertexPerm kind 2 leftFin)
        (localVertexPerm kind 2 rightFin) hmapNe]
      rw [swapKind_twisted]
      simp only [blockSwap_two]
      change hostColorSwap
          (canonicalPalette 2
            (k16Template (kind.twisted 1)
              (localVertexPerm kind 2 leftFin)
              (localVertexPerm kind 2 rightFin))) = _
      have hpreserves :=
        localVertexPerm_preserves kind 2 leftFin rightFin hne
      simp only [blockSwap_two] at hpreserves
      rw [hpreserves]
      have hpalette := hostColorSwap_canonicalPalette (2 : Fin 3)
        ((labelPerm 2).symm
          (k16Template (kind.twisted 1) leftFin rightFin))
      simp only [blockSwap_two] at hpalette
      have hpalette' :
          hostColorSwap
              (canonicalPalette 2
                ((labelPerm 2).symm
                  (k16Template (kind.twisted 1) leftFin rightFin))) =
            canonicalPalette 3
              (labelPerm 2
                ((labelPerm 2).symm
                  (k16Template (kind.twisted 1) leftFin rightFin))) := by
        simpa using hpalette
      rw [hpalette']
      have hleftFin16 : fin16 left = leftFin := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt leftFin.isLt
      have hrightFin16 : fin16 right = rightFin := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt rightFin.isLt
      simp [templateColor, hleftFin16, hrightFin16]

/-! ## Transport of four-row extensions and the three-kind package -/

/-- Transport an exact profile-C four-row extension.  The four free
vertices remain fixed, while all colours and tail vertices are relabelled. -/
noncomputable def transportFourExtension {kind : Kind}
    (ext : FourExtension kind) : FourExtension (swapKind kind) where
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

theorem nonempty_transportFourExtension {kind : Kind} :
    Nonempty (FourExtension kind) →
      Nonempty (FourExtension (swapKind kind)) := by
  rintro ⟨ext⟩
  exact ⟨transportFourExtension ext⟩

/-- Applying the same semantic transport to the swapped kind gives the
reverse implication. -/
theorem nonempty_fourExtension_iff_swapKind (kind : Kind) :
    Nonempty (FourExtension kind) ↔
      Nonempty (FourExtension (swapKind kind)) := by
  constructor
  · exact nonempty_transportFourExtension
  · intro h
    have hback := nonempty_transportFourExtension h
    simpa using hback

/-- Refutations of `uu`, one mixed kind, and `tt` cover all four kinds. -/
structure RepresentativeObstructions : Prop where
  untwisted : ¬Nonempty (FourExtension .uu)
  mixed : ¬Nonempty (FourExtension .ut)
  twisted : ¬Nonempty (FourExtension .tt)

/-- The genuine kind reduction from four exact profile-C formula families
to three representatives. -/
theorem RepresentativeObstructions.universalFourRowObstruction
    (h : RepresentativeObstructions) : UniversalFourRowObstruction := by
  intro kind hext
  cases kind with
  | uu => exact h.untwisted hext
  | ut => exact h.mixed hext
  | tu =>
      apply h.mixed
      have htransported := nonempty_transportFourExtension hext
      rw [swapKind_tu] at htransported
      exact htransported
  | tt => exact h.twisted hext

/-- Consequently, the three representative refutations eliminate the
entire profile-C single-root branch. -/
theorem no_profileC_star_of_representativeObstructions
    (h : RepresentativeObstructions) :
    ¬Nonempty (CanonicalStarWitness ProfileC) :=
  no_profileC_star_of_universalFourRowObstruction
    h.universalFourRowObstruction

#print axioms R4333.ProfileCFourRowKindSymmetry.transportTailWitness
#print axioms R4333.ProfileCFourRowKindSymmetry.transportFourExtension
#print axioms R4333.ProfileCFourRowKindSymmetry.nonempty_fourExtension_iff_swapKind
#print axioms R4333.ProfileCFourRowKindSymmetry.RepresentativeObstructions.universalFourRowObstruction
#print axioms R4333.ProfileCFourRowKindSymmetry.no_profileC_star_of_representativeObstructions

end ProfileCFourRowKindSymmetry
end R4333
