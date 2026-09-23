import R4333Lean.ProfileDToCCompletionTransfer
import R4333Lean.ProfileBThreeRowKindSymmetry

/-!
# Moving a completing free profile-D vertex into a K15

A profile-D four-row object has a `K15 + K15 + K16` tail.  If one of its
four free vertices avoids the omitted colour of the second K15, uniqueness
of a good one-vertex extension of a critical K15 says that its row is the
canonical last row of the corresponding K16.  Moving that free vertex into
the tail leaves three free vertices and a `K15 + K16 + K16` tail, exactly a
profile-B three-row object.

Consequently, after a universal profile-B obstruction has been established,
every free profile-D row must use colour two on the second K15.  The equal
K15 block symmetry gives the corresponding colour-one statement for the
first K15 in a separate CNF layer.
-/

namespace R4333
namespace ProfileDToBFreeCompletionTransfer

open ColoringJoinRows
open SingleRootStarCNF

namespace D
abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev FourVertex := ProfileDFourRowBoundary.FourVertex
abbrev FourExtension := ProfileDFourRowBoundary.FourExtension
abbrev blockVertex := ProfileDTripleJoinReduction.blockVertex
abbrev blockSize := ProfileDTripleJoinReduction.blockSize
abbrev DCoord := (Fin 15 ⊕ Fin 15) ⊕ Fin 16
noncomputable abbrev tailCoordEquiv :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv
end D

namespace B
abbrev Kind := ProfileBRowExtension.Kind
abbrev TailVertex := ProfileBRowExtension.TailVertex
abbrev ThreeVertex := ProfileBThreeRowBoundary.ThreeVertex
abbrev ThreeExtension := ProfileBThreeRowBoundary.ThreeExtension
abbrev blockVertex := ProfileBRowExtension.blockVertex
abbrev blockSize := ProfileBRowExtension.blockSize
abbrev BCoord := Fin 15 ⊕ (Fin 16 ⊕ Fin 16)
abbrev tailDecode := ProfileBThreeRowKindSymmetry.tailDecode
end B

def oldJoined {kind : D.Kind} (ext : D.FourExtension kind) :
    EdgeColoring (Sum D.FourVertex D.TailVertex) (Fin 4) :=
  joinColoring ext.inside ext.tail.coloring ext.rows

theorem oldJoined_noMono {kind : D.Kind} (ext : D.FourExtension kind) :
    NoMonochromaticTriangle (oldJoined ext) := by
  exact (noMono_joinColoring_iff
    ext.inside ext.tail.coloring ext.rows).2
      ⟨ext.insideNoMono, ext.tail.noMono,
        ext.rowsAdmissible, ext.rowsPairCompatible⟩

/-! ## The exact free-vertex completion condition -/

/-- A free vertex supplies the canonical last row of D's second K15. -/
def FreeCompletesSecondK15 {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) : Prop :=
  ∀ x : Fin 15,
    ext.rows moved (D.blockVertex 1 x.val) =
      canonicalPalette 2
        (k16Template (kind.twisted 1) (Fin.last 15) x.castSucc)

/-- Put the old second K15 first and the moved free vertex last. -/
def completionEmbedding (moved : D.FourVertex) :
    Fin 16 → Sum D.FourVertex D.TailVertex :=
  Fin.lastCases (.inl moved)
    (fun x : Fin 15 ↦ .inr (D.blockVertex 1 x.val))

@[simp] theorem completionEmbedding_last (moved : D.FourVertex) :
    completionEmbedding moved (Fin.last 15) = .inl moved :=
  Fin.lastCases_last

@[simp] theorem completionEmbedding_castSucc
    (moved : D.FourVertex) (x : Fin 15) :
    completionEmbedding moved x.castSucc =
      .inr (D.blockVertex 1 x.val) :=
  Fin.lastCases_castSucc x

theorem completionEmbedding_injective (moved : D.FourVertex) :
    Function.Injective (completionEmbedding moved) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
      induction y using Fin.lastCases with
      | last => rfl
      | cast y =>
          rw [completionEmbedding_last,
            completionEmbedding_castSucc] at hxy
          exact (Sum.inl_ne_inr hxy).elim
  | cast x =>
      induction y using Fin.lastCases with
      | last =>
          rw [completionEmbedding_castSucc,
            completionEmbedding_last] at hxy
          exact (Sum.inr_ne_inl hxy).elim
      | cast y =>
          apply Fin.castSucc_injective
          apply Fin.ext
          rw [completionEmbedding_castSucc,
            completionEmbedding_castSucc] at hxy
          have htail : D.blockVertex 1 x.val = D.blockVertex 1 y.val :=
            Sum.inr.inj hxy
          have hval := congrArg Fin.val htail
          rw [ProfileDTripleJoinReduction.blockVertex_val 1 x.isLt,
            ProfileDTripleJoinReduction.blockVertex_val 1 y.isLt] at hval
          simpa [ProfileDTripleJoinReduction.blockStart] using hval

def completionHostColoring {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    EdgeColoring (Fin 16) (Fin 4) :=
  pullbackColoring (oldJoined ext) (completionEmbedding moved)

theorem completionHostColoring_noMono {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    NoMonochromaticTriangle (completionHostColoring ext moved) :=
  noMono_pullback (oldJoined ext) (completionEmbedding moved)
    (completionEmbedding_injective moved) (oldJoined_noMono ext)

/-- Decode a free row which avoids colour two into the local palette of the
second K15. -/
noncomputable def localFreeCompletionRow {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (havoid : ∀ x : Fin 15, ext.rows moved (D.blockVertex 1 x.val) ≠ 2) :
    Fin 15 → ThreeColor := fun x ↦
  (ProfileDFourRowKindSymmetry.canonicalPaletteEquiv 2).symm
    ⟨ext.rows moved (D.blockVertex 1 x.val), havoid x⟩

theorem localFreeCompletionRow_encode {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (havoid : ∀ x : Fin 15, ext.rows moved (D.blockVertex 1 x.val) ≠ 2)
    (x : Fin 15) :
    canonicalPalette 2 (localFreeCompletionRow ext moved havoid x) =
      ext.rows moved (D.blockVertex 1 x.val) := by
  have h := congrArg Subtype.val
    ((ProfileDFourRowKindSymmetry.canonicalPaletteEquiv 2).apply_symm_apply
      ⟨ext.rows moved (D.blockVertex 1 x.val), havoid x⟩)
  exact h

theorem completionHost_eq_paletteLocal {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (havoid : ∀ x : Fin 15, ext.rows moved (D.blockVertex 1 x.val) ≠ 2)
    (u v : Fin 16) (huv : u ≠ v) :
    completionHostColoring ext moved u v =
      canonicalPalette 2
        (extendByLast (k15Template (kind.twisted 1))
          (localFreeCompletionRow ext moved havoid) 0 u v) := by
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast v =>
          simp only [completionHostColoring, pullbackColoring,
            completionEmbedding_last, completionEmbedding_castSucc,
            extendByLast_last_old]
          change ext.rows moved (D.blockVertex 1 v.val) = _
          exact (localFreeCompletionRow_encode ext moved havoid v).symm
  | cast u =>
      induction v using Fin.lastCases with
      | last =>
          rw [(completionHostColoring ext moved).color_symm]
          simp only [completionHostColoring, pullbackColoring,
            completionEmbedding_last, completionEmbedding_castSucc,
            extendByLast_old_last]
          change ext.rows moved (D.blockVertex 1 u.val) = _
          exact (localFreeCompletionRow_encode ext moved havoid u).symm
      | cast v =>
          have huv15 : u ≠ v := by
            intro h
            apply huv
            exact congrArg Fin.castSucc h
          simp only [completionHostColoring, pullbackColoring,
            completionEmbedding_castSucc, extendByLast_old_old]
          change ext.tail.coloring (D.blockVertex 1 u.val)
            (D.blockVertex 1 v.val) = _
          simpa using
            ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
              ext.tail 1 (by decide) u v huv15

theorem localFreeCompletionExtension_good {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (havoid : ∀ x : Fin 15, ext.rows moved (D.blockVertex 1 x.val) ≠ 2) :
    NoMonochromaticTriangle
      (extendByLast (k15Template (kind.twisted 1))
        (localFreeCompletionRow ext moved havoid) 0) := by
  intro x y z hdistinct hmono
  apply completionHostColoring_noMono ext moved x y z hdistinct
  constructor
  · rw [completionHost_eq_paletteLocal ext moved havoid x y hdistinct.1,
      completionHost_eq_paletteLocal ext moved havoid x z hdistinct.2.1]
    exact congrArg (canonicalPalette 2) hmono.1
  · rw [completionHost_eq_paletteLocal ext moved havoid x z hdistinct.2.1,
      completionHost_eq_paletteLocal ext moved havoid y z hdistinct.2.2]
    exact congrArg (canonicalPalette 2) hmono.2

/-- Avoiding the omitted colour is equivalent to supplying the unique
canonical K16 completion row. -/
theorem freeCompletesSecondK15_iff_avoids {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    FreeCompletesSecondK15 ext moved ↔
      ∀ x : Fin 15, ext.rows moved (D.blockVertex 1 x.val) ≠ 2 := by
  constructor
  · intro h x
    rw [h x]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 2 _
  · intro havoid
    have hbase : NoMonochromaticTriangle
        (k15Template (kind.twisted 1)) := by
      cases ht : kind.twisted 1 <;>
        simp [k15Template, k15Untwisted_good, k15Twisted_good]
    have hlocal : localFreeCompletionRow ext moved havoid =
        ProfileDToCCompletionTransfer.canonicalK15LastRow
          (kind.twisted 1) := by
      exact
        (attachment_eq_deficientColor15
          (k15Template (kind.twisted 1)) hbase
          (localFreeCompletionRow ext moved havoid) 0
          (localFreeCompletionExtension_good ext moved havoid)).trans
        (attachment_eq_deficientColor15
          (k15Template (kind.twisted 1)) hbase
          (ProfileDToCCompletionTransfer.canonicalK15LastRow
            (kind.twisted 1)) 0
          (ProfileDToCCompletionTransfer.canonicalK15Extension_good
            (kind.twisted 1))).symm
    intro x
    calc
      ext.rows moved (D.blockVertex 1 x.val) =
          canonicalPalette 2 (localFreeCompletionRow ext moved havoid x) :=
        (localFreeCompletionRow_encode ext moved havoid x).symm
      _ = canonicalPalette 2
          (ProfileDToCCompletionTransfer.canonicalK15LastRow
            (kind.twisted 1) x) := by rw [hlocal]
      _ = canonicalPalette 2
          (k16Template (kind.twisted 1) (Fin.last 15) x.castSucc) := rfl

/-! ## Repartitioning the same fifty vertices -/

def toBKind (kind : D.Kind) : B.Kind :=
  ProfileBRowExtension.Kind.ofBooleans
    (kind.twisted 0) (kind.twisted 1) (kind.twisted 2)

@[simp] theorem toBKind_twisted (kind : D.Kind) (block : Fin 3) :
    (toBKind kind).twisted block = kind.twisted block := by
  fin_cases block <;> simp [toBKind]

/-- Decode the D tail while retaining the free/tail sum. -/
noncomputable def oldCoordEquiv :
    Sum D.FourVertex D.DCoord ≃ Sum D.FourVertex D.TailVertex :=
  Equiv.sumCongr (Equiv.refl D.FourVertex) D.tailCoordEquiv

/-- Coordinates of the old second K15 followed by the moved free vertex. -/
def completionCoord (moved : D.FourVertex) :
    Fin 16 → Sum D.FourVertex D.DCoord :=
  Fin.lastCases (.inl moved)
    (fun x : Fin 15 ↦ .inr (.inl (.inr x)))

@[simp] theorem completionCoord_last (moved : D.FourVertex) :
    completionCoord moved (Fin.last 15) = .inl moved :=
  Fin.lastCases_last

@[simp] theorem completionCoord_castSucc
    (moved : D.FourVertex) (x : Fin 15) :
    completionCoord moved x.castSucc = .inr (.inl (.inr x)) :=
  Fin.lastCases_castSucc x

theorem completionCoord_injective (moved : D.FourVertex) :
    Function.Injective (completionCoord moved) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
      induction y using Fin.lastCases with
      | last => rfl
      | cast y =>
          rw [completionCoord_last, completionCoord_castSucc] at hxy
          exact (Sum.inl_ne_inr hxy).elim
  | cast x =>
      induction y using Fin.lastCases with
      | last =>
          rw [completionCoord_castSucc, completionCoord_last] at hxy
          exact (Sum.inr_ne_inl hxy).elim
      | cast y =>
          rw [completionCoord_castSucc, completionCoord_castSucc] at hxy
          have h : x = y := Sum.inr.inj (Sum.inl.inj (Sum.inr.inj hxy))
          subst y
          rfl

theorem oldCoord_completionCoord (moved : D.FourVertex) (x : Fin 16) :
    oldCoordEquiv (completionCoord moved x) = completionEmbedding moved x := by
  induction x using Fin.lastCases with
  | last =>
      rw [completionCoord_last, completionEmbedding_last]
      rfl
  | cast x =>
      rw [completionCoord_castSucc, completionEmbedding_castSucc]
      exact congrArg Sum.inr
        (ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne x)

/-- The three old free vertices retained after moving `moved`. -/
def freeToOld (moved : D.FourVertex) : B.ThreeVertex → D.FourVertex :=
  fun i ↦ Equiv.swap moved (Fin.last 3) i.castSucc

theorem freeToOld_injective (moved : D.FourVertex) :
    Function.Injective (freeToOld moved) := by
  intro x y hxy
  apply Fin.castSucc_injective
  exact (Equiv.swap moved (Fin.last 3)).injective hxy

theorem freeToOld_ne_moved (moved : D.FourVertex) (i : B.ThreeVertex) :
    freeToOld moved i ≠ moved := by
  intro h
  have hs := congrArg (Equiv.swap moved (Fin.last 3)) h
  simp [freeToOld] at hs
  exact Fin.castSucc_ne_last i hs

theorem freeCoord_ne_completionCoord (moved : D.FourVertex)
    (i : B.ThreeVertex) (z : Fin 16) :
    (.inl (freeToOld moved i) : Sum D.FourVertex D.DCoord) ≠
      completionCoord moved z := by
  induction z using Fin.lastCases with
  | last =>
      rw [completionCoord_last]
      intro h
      exact freeToOld_ne_moved moved i (Sum.inl.inj h)
  | cast z =>
      rw [completionCoord_castSucc]
      exact Sum.inl_ne_inr

def tailCoordEmbedding (moved : D.FourVertex) :
    B.BCoord → Sum D.FourVertex D.DCoord
  | .inl x => .inr (.inl (.inl x))
  | .inr (.inl x) => completionCoord moved x
  | .inr (.inr x) => .inr (.inr x)

theorem tailCoordEmbedding_injective (moved : D.FourVertex) :
    Function.Injective (tailCoordEmbedding moved) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have h : x = y := Sum.inl.inj (Sum.inl.inj (Sum.inr.inj hxy))
          subst y
          rfl
      | inr y =>
          cases y with
          | inl y =>
              induction y using Fin.lastCases with
              | last =>
                  change Sum.inr (Sum.inl (Sum.inl x)) =
                    completionCoord moved (Fin.last 15) at hxy
                  rw [completionCoord_last] at hxy
                  exact (Sum.inr_ne_inl hxy).elim
              | cast y => simp [tailCoordEmbedding, completionCoord] at hxy
          | inr y => simp [tailCoordEmbedding] at hxy
  | inr x =>
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              induction x using Fin.lastCases with
              | last =>
                  change completionCoord moved (Fin.last 15) =
                    Sum.inr (Sum.inl (Sum.inl y)) at hxy
                  rw [completionCoord_last] at hxy
                  exact (Sum.inl_ne_inr hxy).elim
              | cast x => simp [tailCoordEmbedding, completionCoord] at hxy
          | inr y =>
              cases y with
              | inl y =>
                  exact congrArg (fun z ↦ Sum.inr (Sum.inl z))
                    (completionCoord_injective moved hxy)
              | inr y =>
                  induction x using Fin.lastCases with
                  | last =>
                      change completionCoord moved (Fin.last 15) =
                        Sum.inr (Sum.inr y) at hxy
                      rw [completionCoord_last] at hxy
                      exact (Sum.inl_ne_inr hxy).elim
                  | cast x => simp [tailCoordEmbedding, completionCoord] at hxy
      | inr x =>
          cases y with
          | inl y => simp [tailCoordEmbedding] at hxy
          | inr y =>
              cases y with
              | inl y =>
                  induction y using Fin.lastCases with
                  | last =>
                      change Sum.inr (Sum.inr x) =
                        completionCoord moved (Fin.last 15) at hxy
                      rw [completionCoord_last] at hxy
                      exact (Sum.inr_ne_inl hxy).elim
                  | cast y => simp [tailCoordEmbedding, completionCoord] at hxy
              | inr y =>
                  have h : x = y := Sum.inr.inj (Sum.inr.inj hxy)
                  subst y
                  rfl

noncomputable def newTailToOld (moved : D.FourVertex) :
    B.TailVertex → Sum D.FourVertex D.TailVertex :=
  fun x ↦ oldCoordEquiv (tailCoordEmbedding moved (B.tailDecode x))

theorem newTailToOld_injective (moved : D.FourVertex) :
    Function.Injective (newTailToOld moved) := by
  intro x y hxy
  apply B.tailDecode.injective
  apply tailCoordEmbedding_injective moved
  apply oldCoordEquiv.injective
  exact hxy

@[simp] theorem newTail_block_zero (moved : D.FourVertex) (i : Fin 15) :
    newTailToOld moved (B.blockVertex 0 i.val) =
      .inr (D.blockVertex 0 i.val) := by
  rw [newTailToOld, ProfileBThreeRowKindSymmetry.tailDecode_block_zero]
  exact congrArg Sum.inr
    (ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero i)

@[simp] theorem newTail_block_one (moved : D.FourVertex) (i : Fin 16) :
    newTailToOld moved (B.blockVertex 1 i.val) =
      completionEmbedding moved i := by
  rw [newTailToOld, ProfileBThreeRowKindSymmetry.tailDecode_block_one]
  exact oldCoord_completionCoord moved i

@[simp] theorem newTail_block_two (moved : D.FourVertex) (i : Fin 16) :
    newTailToOld moved (B.blockVertex 2 i.val) =
      .inr (D.blockVertex 2 i.val) := by
  rw [newTailToOld, ProfileBThreeRowKindSymmetry.tailDecode_block_two]
  exact congrArg Sum.inr
    (ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo i)

/-! ## The resulting profile-B tail and three-row extension -/

noncomputable def newTailColoring {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    EdgeColoring B.TailVertex (Fin 4) :=
  pullbackColoring (oldJoined ext) (newTailToOld moved)

theorem completionHost_eq_canonical {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (hcomplete : FreeCompletesSecondK15 ext moved)
    (u v : Fin 16) (huv : u ≠ v) :
    completionHostColoring ext moved u v =
      canonicalPalette 2 (k16Template (kind.twisted 1) u v) := by
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast v =>
          simp only [completionHostColoring, pullbackColoring,
            completionEmbedding_last, completionEmbedding_castSucc]
          change ext.rows moved (D.blockVertex 1 v.val) = _
          exact hcomplete v
  | cast u =>
      induction v using Fin.lastCases with
      | last =>
          rw [(completionHostColoring ext moved).color_symm]
          simp only [completionHostColoring, pullbackColoring,
            completionEmbedding_last, completionEmbedding_castSucc]
          change ext.rows moved (D.blockVertex 1 u.val) = _
          rw [hcomplete u, (k16Template (kind.twisted 1)).color_symm]
      | cast v =>
          have huv15 : u ≠ v := by
            intro h
            apply huv
            exact congrArg Fin.castSucc h
          simp only [completionHostColoring, pullbackColoring,
            completionEmbedding_castSucc]
          change ext.tail.coloring (D.blockVertex 1 u.val)
            (D.blockVertex 1 v.val) = _
          simpa [k15Template_edge_eq_k16Template] using
            ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
              ext.tail 1 (by decide) u v huv15

theorem newTail_templateCanonical {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (hcomplete : FreeCompletesSecondK15 ext moved)
    (block : Fin 3) (left right : Nat)
    (hleft : left < B.blockSize block)
    (hright : right < B.blockSize block) (hlr : left < right) :
    newTailColoring ext moved
        (B.blockVertex block left) (B.blockVertex block right) =
      canonicalPalette (Fin.succ block)
        (templateColor (B.blockSize block)
          ((toBKind kind).twisted block) left right) := by
  fin_cases block
  · let u : Fin 15 := ⟨left, by
      simpa [ProfileBRowExtension.blockSize] using hleft⟩
    let v : Fin 15 := ⟨right, by
      simpa [ProfileBRowExtension.blockSize] using hright⟩
    have huv : u ≠ v := Fin.ne_of_lt (by simpa [u, v] using hlr)
    change (oldJoined ext)
      (newTailToOld moved (B.blockVertex 0 u.val))
      (newTailToOld moved (B.blockVertex 0 v.val)) = _
    rw [newTail_block_zero, newTail_block_zero]
    change ext.tail.coloring (D.blockVertex 0 u.val)
      (D.blockVertex 0 v.val) = _
    have hcanonical := ext.tail.templateCanonical 0 u.val v.val
      (by simp [ProfileDTripleJoinReduction.blockSize])
      (by simp [ProfileDTripleJoinReduction.blockSize])
      (by simpa [u, v] using hlr)
    have hleft15 : left < 15 := u.isLt
    have hright15 : right < 15 := v.isLt
    simpa [ProfileBRowExtension.blockSize,
      ProfileDTripleJoinReduction.blockSize, templateColor, fin15,
      Nat.mod_eq_of_lt hleft15, Nat.mod_eq_of_lt hright15, u, v]
      using hcanonical
  · let u : Fin 16 := ⟨left, by
      simpa [ProfileBRowExtension.blockSize] using hleft⟩
    let v : Fin 16 := ⟨right, by
      simpa [ProfileBRowExtension.blockSize] using hright⟩
    have huv : u ≠ v := Fin.ne_of_lt (by simpa [u, v] using hlr)
    change (oldJoined ext)
      (newTailToOld moved (B.blockVertex 1 u.val))
      (newTailToOld moved (B.blockVertex 1 v.val)) = _
    rw [newTail_block_one, newTail_block_one]
    have hcanonical := completionHost_eq_canonical
      ext moved hcomplete u v huv
    have hleft16 : left < 16 := u.isLt
    have hright16 : right < 16 := v.isLt
    simpa [completionHostColoring, pullbackColoring,
      ProfileBRowExtension.blockSize, templateColor, fin16,
      Nat.mod_eq_of_lt hleft16, Nat.mod_eq_of_lt hright16, u, v]
      using hcanonical
  · let u : Fin 16 := ⟨left, by
      simpa [ProfileBRowExtension.blockSize] using hleft⟩
    let v : Fin 16 := ⟨right, by
      simpa [ProfileBRowExtension.blockSize] using hright⟩
    have huv : u ≠ v := Fin.ne_of_lt (by simpa [u, v] using hlr)
    change (oldJoined ext)
      (newTailToOld moved (B.blockVertex 2 u.val))
      (newTailToOld moved (B.blockVertex 2 v.val)) = _
    rw [newTail_block_two, newTail_block_two]
    change ext.tail.coloring (D.blockVertex 2 u.val)
      (D.blockVertex 2 v.val) = _
    have hcanonical := ext.tail.templateCanonical 2 u.val v.val
      (by simp [ProfileDTripleJoinReduction.blockSize])
      (by simp [ProfileDTripleJoinReduction.blockSize])
      (by simpa [u, v] using hlr)
    have hleft16 : left < 16 := u.isLt
    have hright16 : right < 16 := v.isLt
    simpa [ProfileBRowExtension.blockSize,
      ProfileDTripleJoinReduction.blockSize, templateColor, fin16,
      Nat.mod_eq_of_lt hleft16, Nat.mod_eq_of_lt hright16, u, v]
      using hcanonical

noncomputable def newTailWitness {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (hcomplete : FreeCompletesSecondK15 ext moved) :
    ProfileBRowExtension.TailWitness (toBKind kind) where
  coloring := newTailColoring ext moved
  noMono := noMono_pullback (oldJoined ext) (newTailToOld moved)
    (newTailToOld_injective moved) (oldJoined_noMono ext)
  rootForbidden := by
    intro block left right hleft hright hlr
    rw [newTail_templateCanonical ext moved hcomplete block left right
      hleft hright hlr]
    exact SingleRootStarWitness61.canonicalPalette_ne_block
      (Fin.succ block) _
  templateCanonical := by
    intro block _hcritical left right hleft hright hlr
    exact newTail_templateCanonical ext moved hcomplete block left right
      hleft hright hlr

def newFreeToOld (moved : D.FourVertex) :
    B.ThreeVertex → Sum D.FourVertex D.TailVertex :=
  fun i ↦ .inl (freeToOld moved i)

noncomputable def newSplitToOld (moved : D.FourVertex) :
    Sum B.ThreeVertex B.TailVertex →
      Sum D.FourVertex D.TailVertex
  | .inl i => newFreeToOld moved i
  | .inr x => newTailToOld moved x

theorem newSplitToOld_injective (moved : D.FourVertex) :
    Function.Injective (newSplitToOld moved) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl (freeToOld_injective moved (Sum.inl.inj hxy))
      | inr y =>
          have hcoord := congrArg oldCoordEquiv.symm hxy
          simp only [newSplitToOld, newFreeToOld, newTailToOld,
            Equiv.symm_apply_apply] at hcoord
          change .inl (freeToOld moved x) =
            tailCoordEmbedding moved (B.tailDecode y) at hcoord
          generalize hy : B.tailDecode y = coord at hcoord
          cases coord with
          | inl i => simp [tailCoordEmbedding] at hcoord
          | inr i =>
              cases i with
              | inl i =>
                  exact (freeCoord_ne_completionCoord moved x i hcoord).elim
              | inr i => simp [tailCoordEmbedding] at hcoord
  | inr x =>
      cases y with
      | inl y =>
          have hcoord := congrArg oldCoordEquiv.symm hxy
          simp only [newSplitToOld, newFreeToOld, newTailToOld,
            Equiv.symm_apply_apply] at hcoord
          change tailCoordEmbedding moved (B.tailDecode x) =
            .inl (freeToOld moved y) at hcoord
          generalize hx : B.tailDecode x = coord at hcoord
          cases coord with
          | inl i => simp [tailCoordEmbedding] at hcoord
          | inr i =>
              cases i with
              | inl i =>
                  exact (freeCoord_ne_completionCoord moved y i hcoord.symm).elim
              | inr i => simp [tailCoordEmbedding] at hcoord
      | inr y =>
          exact congrArg Sum.inr (newTailToOld_injective moved hxy)

noncomputable def newInside {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    EdgeColoring B.ThreeVertex (Fin 4) :=
  pullbackColoring (oldJoined ext) (newFreeToOld moved)

noncomputable def newRows {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    B.ThreeVertex → B.TailVertex → Fin 4 :=
  fun a x ↦ (oldJoined ext) (newFreeToOld moved a)
    (newTailToOld moved x)

theorem newJoin_eq_pullback {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    joinColoring (newInside ext moved) (newTailColoring ext moved)
        (newRows ext moved) =
      pullbackColoring (oldJoined ext) (newSplitToOld moved) := by
  ext u v
  cases u <;> cases v <;>
    simp [joinColoring, newInside, newTailColoring, newRows,
      newSplitToOld, pullbackColoring, (oldJoined ext).color_symm]

theorem newJoin_noMono {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    NoMonochromaticTriangle
      (joinColoring (newInside ext moved) (newTailColoring ext moved)
        (newRows ext moved)) := by
  rw [newJoin_eq_pullback]
  exact noMono_pullback (oldJoined ext) (newSplitToOld moved)
    (newSplitToOld_injective moved) (oldJoined_noMono ext)

theorem newInside_rootForbidden {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex) :
    ∀ a b : B.ThreeVertex, a ≠ b → newInside ext moved a b ≠ 0 := by
  intro a b hab
  change ext.inside (freeToOld moved a) (freeToOld moved b) ≠ 0
  apply ext.insideRootForbidden
  exact (freeToOld_injective moved).ne hab

/-- Move a free completion vertex into D's second K15.  The displayed
block sizes change from `4 + (15+15+16)` to `3 + (15+16+16)` while the
three template selector bits are unchanged. -/
noncomputable def transferSecondWith {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : D.FourVertex)
    (hcomplete : FreeCompletesSecondK15 ext moved) :
    B.ThreeExtension (toBKind kind) := by
  have hdecomp := (noMono_joinColoring_iff
    (newInside ext moved) (newTailColoring ext moved)
      (newRows ext moved)).1 (newJoin_noMono ext moved)
  exact {
    tail := newTailWitness ext moved hcomplete
    inside := newInside ext moved
    rows := newRows ext moved
    insideNoMono := hdecomp.1
    insideRootForbidden := newInside_rootForbidden ext moved
    rowsAdmissible := hdecomp.2.2.1
    rowsPairCompatible := hdecomp.2.2.2
  }

/-- Under a universal profile-B obstruction, every free D row uses the
second K15's omitted colour two somewhere on that block. -/
theorem every_free_row_hits_secondK15_of_B_obstruction
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : D.Kind} (ext : D.FourExtension kind) :
    ∀ moved : D.FourVertex, ∃ x : Fin 15,
      ext.rows moved (D.blockVertex 1 x.val) = 2 := by
  intro moved
  by_contra hnone
  push Not at hnone
  have hcomplete :=
    (freeCompletesSecondK15_iff_avoids ext moved).2 hnone
  exact hB (toBKind kind) ⟨transferSecondWith ext moved hcomplete⟩

theorem hostColorPerm_one_eq_two :
    ProfileDFourRowKindSymmetry.hostColorPerm 1 = 2 := by
  simpa using
    (ProfileDFourRowKindSymmetry.hostColorPerm_succ_apply (1 : Fin 3))

/-- The equal-K15 symmetry turns the preceding theorem into the opposite
orientation: every free row also uses colour one on D's first K15. -/
theorem every_free_row_hits_firstK15_of_B_obstruction
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : D.Kind} (ext : D.FourExtension kind) :
    ∀ moved : D.FourVertex, ∃ x : Fin 15,
      ext.rows moved (D.blockVertex 0 x.val) = 1 := by
  intro moved
  let transported :=
    ProfileDFourRowKindSymmetry.transportFourExtension ext
  obtain ⟨x, hx⟩ :=
    every_free_row_hits_secondK15_of_B_obstruction hB transported moved
  refine ⟨ProfileDFourRowKindSymmetry.localK15One kind x, ?_⟩
  change ProfileDFourRowKindSymmetry.hostColorPerm
      (ext.rows moved
        (ProfileDFourRowKindSymmetry.tailVertexPerm kind
          (D.blockVertex 1 x.val))) = 2 at hx
  rw [ProfileDFourRowKindSymmetry.tailVertexPerm_blockOne] at hx
  apply ProfileDFourRowKindSymmetry.hostColorPerm.injective
  rw [hostColorPerm_one_eq_two]
  exact hx

#print axioms R4333.ProfileDToBFreeCompletionTransfer.freeCompletesSecondK15_iff_avoids
#print axioms R4333.ProfileDToBFreeCompletionTransfer.transferSecondWith
#print axioms R4333.ProfileDToBFreeCompletionTransfer.every_free_row_hits_secondK15_of_B_obstruction
#print axioms R4333.ProfileDToBFreeCompletionTransfer.every_free_row_hits_firstK15_of_B_obstruction

end ProfileDToBFreeCompletionTransfer
end R4333
