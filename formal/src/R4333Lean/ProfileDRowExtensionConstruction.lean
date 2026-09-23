import R4333Lean.ProfileDRowExtension

/-!
# Reconstructing a profile-D star from exact full row-extension data

`ProfileDRowExtension.extensionOfStar` records the exact fourteen-row object
obtained by deleting the first block of a canonical profile-D star.  This file
proves the converse: the row-extension structure already contains all data
needed to reconstruct that star.

This closes a semantic gap which is important for structural transfers.  A
statement about every full profile-D row extension is now literally equivalent
to a statement about every canonical profile-D star, rather than merely being
a necessary relaxation.
-/

namespace R4333
namespace ProfileDRowExtensionConstruction

open SingleRootStarCNF
open SingleRootStarWitness61
open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension

/-- The consecutive free/tail decomposition is an equivalence because it is
injective and both sides have sixty elements. -/
noncomputable def splitEquiv : Sum FreeVertex TailVertex ≃ Fin 60 :=
  Equiv.ofBijective splitToFin
    ((Fintype.bijective_iff_injective_and_card splitToFin).2
      ⟨splitToFin_injective, by simp [FreeVertex, TailVertex]⟩)

@[simp] theorem splitEquiv_apply (x : Sum FreeVertex TailVertex) :
    splitEquiv x = splitToFin x := rfl

@[simp] theorem splitEquiv_symm_freeEmbedding (a : FreeVertex) :
    splitEquiv.symm (freeEmbedding a) = Sum.inl a := by
  apply splitEquiv.injective
  simp [splitEquiv, splitToFin]

@[simp] theorem splitEquiv_symm_tailEmbedding (x : TailVertex) :
    splitEquiv.symm (tailEmbedding x) = Sum.inr x := by
  apply splitEquiv.injective
  simp [splitEquiv, splitToFin]

/-- The full non-root colouring encoded by an exact row extension. -/
noncomputable def fullColoring {kind : Kind} (ext : Extension kind) :
    EdgeColoring (Fin 60) (Fin 4) :=
  pullbackColoring
    (joinColoring ext.inside ext.tail.coloring ext.rows) splitEquiv.symm

@[simp] theorem fullColoring_free_free {kind : Kind} (ext : Extension kind)
    (a b : FreeVertex) :
    fullColoring ext (freeEmbedding a) (freeEmbedding b) = ext.inside a b := by
  change (joinColoring ext.inside ext.tail.coloring ext.rows)
    (splitEquiv.symm (freeEmbedding a))
    (splitEquiv.symm (freeEmbedding b)) = ext.inside a b
  rw [splitEquiv_symm_freeEmbedding, splitEquiv_symm_freeEmbedding]
  rfl

@[simp] theorem fullColoring_tail_tail {kind : Kind} (ext : Extension kind)
    (x y : TailVertex) :
    fullColoring ext (tailEmbedding x) (tailEmbedding y) =
      ext.tail.coloring x y := by
  change (joinColoring ext.inside ext.tail.coloring ext.rows)
    (splitEquiv.symm (tailEmbedding x))
    (splitEquiv.symm (tailEmbedding y)) = ext.tail.coloring x y
  rw [splitEquiv_symm_tailEmbedding, splitEquiv_symm_tailEmbedding]
  rfl

@[simp] theorem fullColoring_free_tail {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) (x : TailVertex) :
    fullColoring ext (freeEmbedding a) (tailEmbedding x) = ext.rows a x := by
  change (joinColoring ext.inside ext.tail.coloring ext.rows)
    (splitEquiv.symm (freeEmbedding a))
    (splitEquiv.symm (tailEmbedding x)) = ext.rows a x
  rw [splitEquiv_symm_freeEmbedding, splitEquiv_symm_tailEmbedding]
  rfl

theorem joinedNoMono {kind : Kind} (ext : Extension kind) :
    NoMonochromaticTriangle
      (joinColoring ext.inside ext.tail.coloring ext.rows) :=
  (noMono_joinColoring_iff ext.inside ext.tail.coloring ext.rows).2
    ⟨ext.insideNoMono, ext.tail.noMono, ext.rowsAdmissible,
      ext.rowsPairCompatible⟩

theorem fullColoring_noMono {kind : Kind} (ext : Extension kind) :
    NoMonochromaticTriangle (fullColoring ext) :=
  noMono_pullback _ splitEquiv.symm splitEquiv.symm.injective
    (joinedNoMono ext)

/-- The first block is noncritical, so its selector is irrelevant.  The other
three selectors are exactly the kind carried by the tail witness. -/
def chosenTemplate (kind : Kind) : Fin 4 → Bool :=
  ![false, kind.twisted 0, kind.twisted 1, kind.twisted 2]

theorem fullColoring_firstBlock {kind : Kind} (ext : Extension kind)
    (left right : Nat) (hleft : left < 14) (hright : right < 14) :
    fullColoring ext
        (blockVertex ProfileD 0 left) (blockVertex ProfileD 0 right) =
      ext.inside ⟨left, hleft⟩ ⟨right, hright⟩ := by
  rw [star_blockVertex_zero_eq_freeEmbedding left hleft,
    star_blockVertex_zero_eq_freeEmbedding right hright]
  simpa [freeEmbedding] using
    (fullColoring_free_free ext
      (⟨left, hleft⟩ : FreeVertex) (⟨right, hright⟩ : FreeVertex))

theorem fullColoring_tailBlock {kind : Kind} (ext : Extension kind)
    (block : Fin 3) (left right : Nat)
    (hleft : left < ProfileDTripleJoinReduction.blockSize block)
    (hright : right < ProfileDTripleJoinReduction.blockSize block) :
    fullColoring ext
        (blockVertex ProfileD (Fin.succ block) left)
        (blockVertex ProfileD (Fin.succ block) right) =
      ext.tail.coloring
        (ProfileDTripleJoinReduction.blockVertex block left)
        (ProfileDTripleJoinReduction.blockVertex block right) := by
  rw [← tailEmbedding_blockVertex block left hleft,
    ← tailEmbedding_blockVertex block right hright]
  exact fullColoring_tail_tail ext _ _

theorem fullColoring_tailBlock_rootForbidden {kind : Kind}
    (ext : Extension kind) (block : Fin 3) (left right : Nat)
    (hleft : left < ProfileDTripleJoinReduction.blockSize block)
    (hright : right < ProfileDTripleJoinReduction.blockSize block)
    (hlr : left < right) :
    fullColoring ext
        (blockVertex ProfileD (Fin.succ block) left)
        (blockVertex ProfileD (Fin.succ block) right) ≠ Fin.succ block := by
  rw [fullColoring_tailBlock ext block left right hleft hright,
    ext.tail.templateCanonical block left right hleft hright hlr]
  exact canonicalPalette_ne_block (Fin.succ block) _

theorem fullColoring_tailBlock_template {kind : Kind}
    (ext : Extension kind) (block : Fin 3) (left right : Nat)
    (hleft : left < ProfileDTripleJoinReduction.blockSize block)
    (hright : right < ProfileDTripleJoinReduction.blockSize block)
    (hlr : left < right) :
    fullColoring ext
        (blockVertex ProfileD (Fin.succ block) left)
        (blockVertex ProfileD (Fin.succ block) right) =
      canonicalPalette (Fin.succ block)
        (templateColor (SingleRootStarCNF.blockSize ProfileD (Fin.succ block))
          (chosenTemplate kind (Fin.succ block)) left right) := by
  rw [fullColoring_tailBlock ext block left right hleft hright,
    ext.tail.templateCanonical block left right hleft hright hlr]
  congr 2
  · exact (star_blockSize_tail block).symm
  · fin_cases block <;> rfl

theorem fullColoring_rootForbidden {kind : Kind} (ext : Extension kind) :
    ∀ (block : Fin 4) (left right : Nat),
      left < SingleRootStarCNF.blockSize ProfileD block →
      right < SingleRootStarCNF.blockSize ProfileD block → left < right →
      fullColoring ext (blockVertex ProfileD block left)
        (blockVertex ProfileD block right) ≠ block := by
  intro block left right hleft hright hlr
  fin_cases block
  · have hleft' : left < 14 := by
      simpa [SingleRootStarCNF.blockSize, profileSizes] using hleft
    have hright' : right < 14 := by
      simpa [SingleRootStarCNF.blockSize, profileSizes] using hright
    rw [fullColoring_firstBlock ext left right hleft' hright']
    apply ext.insideRootForbidden
    exact Fin.ne_of_lt hlr
  · have hleft' :
        left < ProfileDTripleJoinReduction.blockSize (0 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hleft
    have hright' :
        right < ProfileDTripleJoinReduction.blockSize (0 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hright
    simpa using
      (fullColoring_tailBlock_rootForbidden ext 0 left right
        hleft' hright' hlr)
  · have hleft' :
        left < ProfileDTripleJoinReduction.blockSize (1 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hleft
    have hright' :
        right < ProfileDTripleJoinReduction.blockSize (1 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hright
    simpa using
      (fullColoring_tailBlock_rootForbidden ext 1 left right
        hleft' hright' hlr)
  · have hleft' :
        left < ProfileDTripleJoinReduction.blockSize (2 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hleft
    have hright' :
        right < ProfileDTripleJoinReduction.blockSize (2 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hright
    simpa using
      (fullColoring_tailBlock_rootForbidden ext 2 left right
        hleft' hright' hlr)

theorem fullColoring_templateCanonical {kind : Kind} (ext : Extension kind) :
    ∀ (block : Fin 4), isCriticalBlock ProfileD block →
      ∀ (left right : Nat),
        left < SingleRootStarCNF.blockSize ProfileD block →
        right < SingleRootStarCNF.blockSize ProfileD block → left < right →
        fullColoring ext (blockVertex ProfileD block left)
            (blockVertex ProfileD block right) =
          canonicalPalette block
            (templateColor (SingleRootStarCNF.blockSize ProfileD block)
              (chosenTemplate kind block) left right) := by
  intro block hcritical left right hleft hright hlr
  fin_cases block
  · simp [isCriticalBlock, SingleRootStarCNF.blockSize, profileSizes] at hcritical
  · have hleft' :
        left < ProfileDTripleJoinReduction.blockSize (0 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hleft
    have hright' :
        right < ProfileDTripleJoinReduction.blockSize (0 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hright
    simpa using
      (fullColoring_tailBlock_template ext 0 left right hleft' hright' hlr)
  · have hleft' :
        left < ProfileDTripleJoinReduction.blockSize (1 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hleft
    have hright' :
        right < ProfileDTripleJoinReduction.blockSize (1 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hright
    simpa using
      (fullColoring_tailBlock_template ext 1 left right hleft' hright' hlr)
  · have hleft' :
        left < ProfileDTripleJoinReduction.blockSize (2 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hleft
    have hright' :
        right < ProfileDTripleJoinReduction.blockSize (2 : Fin 3) := by
      simpa [SingleRootStarCNF.blockSize, profileSizes,
        ProfileDTripleJoinReduction.blockSize] using hright
    simpa using
      (fullColoring_tailBlock_template ext 2 left right hleft' hright' hlr)

/-- Exact converse to `extensionOfStar`: a full row extension is already a
canonical profile-D star witness. -/
noncomputable def starOfExtension {kind : Kind} (ext : Extension kind) :
    CanonicalStarWitness ProfileD where
  coloring := fullColoring ext
  noMono := fullColoring_noMono ext
  chosenTemplate := chosenTemplate kind
  rootForbidden := fullColoring_rootForbidden ext
  templateCanonical := fullColoring_templateCanonical ext

theorem nonempty_star_of_nonempty_extension {kind : Kind}
    (h : Nonempty (Extension kind)) :
    Nonempty (CanonicalStarWitness ProfileD) := by
  rcases h with ⟨ext⟩
  exact ⟨starOfExtension ext⟩

/-- The profile-D star exists exactly when one of its eight full exact row
extensions exists. -/
theorem nonempty_profileD_star_iff_exists_extension :
    Nonempty (CanonicalStarWitness ProfileD) ↔
      ∃ kind : Kind, Nonempty (Extension kind) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨kindOfWitness w, ⟨extensionOfStar w⟩⟩
  · rintro ⟨kind, hext⟩
    exact nonempty_star_of_nonempty_extension hext

/-- Obstruction form of the exact equivalence. -/
theorem no_profileD_star_iff_all_extensions_empty :
    (¬Nonempty (CanonicalStarWitness ProfileD)) ↔
      ∀ kind : Kind, ¬Nonempty (Extension kind) := by
  constructor
  · intro hstar kind hext
    exact hstar (nonempty_star_of_nonempty_extension hext)
  · intro hall hstar
    obtain ⟨kind, hext⟩ :=
      nonempty_profileD_star_iff_exists_extension.mp hstar
    exact hall kind hext

#print axioms R4333.ProfileDRowExtensionConstruction.splitEquiv
#print axioms R4333.ProfileDRowExtensionConstruction.fullColoring_noMono
#print axioms R4333.ProfileDRowExtensionConstruction.starOfExtension
#print axioms R4333.ProfileDRowExtensionConstruction.nonempty_profileD_star_iff_exists_extension
#print axioms R4333.ProfileDRowExtensionConstruction.no_profileD_star_iff_all_extensions_empty

end ProfileDRowExtensionConstruction
end R4333
