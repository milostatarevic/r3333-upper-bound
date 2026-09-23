import R4333Lean.ProfileDDegreeTenNeighborhoodCatalogueEntrance61
import R4333Lean.ProfileDDegreeTenNeighborhoodPartition61
import R4333Lean.K15DeficientCertificate
import R4333Lean.CriticalCatalogues

/-!
# Restoring the global root at a degree-ten profile-D endpoint

The fifteen own-colour neighbours isolated in
`ProfileDDegreeTenNeighborhoodCatalogueEntrance61` split into the five
retained free vertices and two foreign five-sets.  In the original rooted
picture the deleted global root sees these groups in the three colours other
than the selected endpoint's own colour.

This file restores that root as the last vertex.  The resulting decoded
three-colouring of `K16` is triangle-free, its attachment row is forced to be
the canonical deficient-colour row of the critical `K15`, and the checked
`K16` catalogue identifies it with one of the two critical templates.  Thus
the local configuration is compatible but completely rigid: the selected
endpoint is a fourth-colour cone over a critical three-colour `K16`.
-/

namespace R4333
namespace ProfileDDegreeTenRestoredRootK16

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDDegreeTenNeighborhoodCatalogueEntrance61
open ProfileDDegreeTenNeighborhoodPartition61
open CriticalK15PartitionClassification

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FiveSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension
abbrev DegreeTenSkeleton {kind : Kind} (ext : FiveSupportExtension kind) :=
  ProfileDDegreeTenNeighborhoodCatalogueEntrance61.ThreeC5Skeleton ext

/-! ## The restored root row -/

/-- The host colour from the deleted global root to a labelled neighbour.
The three coordinate summands are exactly its three non-own root blocks. -/
def restoredRootHostAttachment {kind : Kind}
    (ext : FiveSupportExtension kind) (i : Fin 15) : Fin 4 :=
  match threeFiveEquiv.symm i with
  | .inl (.inl _) => freeHostForbiddenColor
  | .inl (.inr _) => firstForeignHostForbiddenColor ext
  | .inr _ => secondForeignHostForbiddenColor ext

@[simp] theorem restoredRootHostAttachment_freeLabel {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext (freeLabel a) =
      freeHostForbiddenColor := by
  simp [restoredRootHostAttachment, freeLabel]

@[simp] theorem restoredRootHostAttachment_firstForeignLabel {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext (firstForeignLabel a) =
      firstForeignHostForbiddenColor ext := by
  simp [restoredRootHostAttachment, firstForeignLabel]

@[simp] theorem restoredRootHostAttachment_secondForeignLabel {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext (secondForeignLabel a) =
      secondForeignHostForbiddenColor ext := by
  simp [restoredRootHostAttachment, secondForeignLabel]

@[simp] theorem restoredRootHostAttachment_freeCoordinate {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext (threeFiveEquiv (.inl (.inl a))) =
      freeHostForbiddenColor := by
  simpa [freeLabel] using restoredRootHostAttachment_freeLabel ext a

@[simp] theorem restoredRootHostAttachment_firstForeignCoordinate
    {kind : Kind} (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext (threeFiveEquiv (.inl (.inr a))) =
      firstForeignHostForbiddenColor ext := by
  simpa [firstForeignLabel] using
    restoredRootHostAttachment_firstForeignLabel ext a

@[simp] theorem restoredRootHostAttachment_secondForeignCoordinate
    {kind : Kind} (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext (threeFiveEquiv (.inr a)) =
      secondForeignHostForbiddenColor ext := by
  simpa [secondForeignLabel] using
    restoredRootHostAttachment_secondForeignLabel ext a

/-- Decode the restored root row through the three colours complementary to
the selected endpoint's own colour. -/
noncomputable def restoredRootAttachment {kind : Kind}
    (ext : FiveSupportExtension kind) (i : Fin 15) : ThreeColor :=
  decodeNonBlockColor (blockRootColor ext.block)
    (restoredRootHostAttachment ext i)

@[simp] theorem restoredRootAttachment_freeLabel {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootAttachment ext (freeLabel a) = freeForbiddenColor ext := by
  simp [restoredRootAttachment, freeForbiddenColor]

@[simp] theorem restoredRootAttachment_firstForeignLabel {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootAttachment ext (firstForeignLabel a) =
      firstForeignForbiddenColor ext := by
  simp [restoredRootAttachment, firstForeignForbiddenColor]

@[simp] theorem restoredRootAttachment_secondForeignLabel {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootAttachment ext (secondForeignLabel a) =
      secondForeignForbiddenColor ext := by
  simp [restoredRootAttachment, secondForeignForbiddenColor]

@[simp] theorem restoredRootAttachment_freeCoordinate {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootAttachment ext (threeFiveEquiv (.inl (.inl a))) =
      freeForbiddenColor ext := by
  simpa [freeLabel] using restoredRootAttachment_freeLabel ext a

@[simp] theorem restoredRootAttachment_firstForeignCoordinate {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootAttachment ext (threeFiveEquiv (.inl (.inr a))) =
      firstForeignForbiddenColor ext := by
  simpa [firstForeignLabel] using
    restoredRootAttachment_firstForeignLabel ext a

@[simp] theorem restoredRootAttachment_secondForeignCoordinate {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    restoredRootAttachment ext (threeFiveEquiv (.inr a)) =
      secondForeignForbiddenColor ext := by
  simpa [secondForeignLabel] using
    restoredRootAttachment_secondForeignLabel ext a

theorem freeHostForbiddenColor_ne_firstForeignHostForbiddenColor
    {kind : Kind} (ext : FiveSupportExtension kind) :
    freeHostForbiddenColor ≠ firstForeignHostForbiddenColor ext := by
  exact fun h => (blockRootColor_ne_zero (firstForeignBlock ext.block)) h.symm

theorem freeHostForbiddenColor_ne_secondForeignHostForbiddenColor
    {kind : Kind} (ext : FiveSupportExtension kind) :
    freeHostForbiddenColor ≠ secondForeignHostForbiddenColor ext := by
  exact fun h => (blockRootColor_ne_zero (secondForeignBlock ext.block)) h.symm

theorem firstForeignHostForbiddenColor_ne_secondForeignHostForbiddenColor
    {kind : Kind} (ext : FiveSupportExtension kind) :
    firstForeignHostForbiddenColor ext ≠
      secondForeignHostForbiddenColor ext := by
  exact blockRootColor_ne_of_block_ne
    (firstForeignBlock_ne_second ext.block)

/-! ## Validity of the restored attachment -/

/-- Equal restored host colours force the old edge to avoid their common
colour.  This is precisely the one-vertex-extension compatibility law. -/
theorem restoredRootHostAttachment_compatible {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext)
    {u v : Fin 15} (huv : u ≠ v)
    (hattachment : restoredRootHostAttachment ext u =
      restoredRootHostAttachment ext v) :
    ownNeighborhoodHostColoring skeleton u v ≠
      restoredRootHostAttachment ext u := by
  let cu := threeFiveEquiv.symm u
  let cv := threeFiveEquiv.symm v
  have hu : u = threeFiveEquiv cu :=
    (threeFiveEquiv.apply_symm_apply u).symm
  have hv : v = threeFiveEquiv cv :=
    (threeFiveEquiv.apply_symm_apply v).symm
  rw [hu, hv] at huv hattachment ⊢
  rcases cu with (left | second)
  · rcases left with (free | first)
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · simpa only [restoredRootHostAttachment_freeCoordinate] using
            (freeLabels_hostIndependent skeleton
              (threeFiveEquiv (.inl (.inl free)))
              (Finset.mem_image.mpr ⟨free, by simp, rfl⟩)
              (threeFiveEquiv (.inl (.inl free')))
              (Finset.mem_image.mpr ⟨free', by simp, rfl⟩) huv)
        · exact (freeHostForbiddenColor_ne_firstForeignHostForbiddenColor
            ext (by simpa using hattachment)).elim
      · exact (freeHostForbiddenColor_ne_secondForeignHostForbiddenColor
          ext (by simpa using hattachment)).elim
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · exact (freeHostForbiddenColor_ne_firstForeignHostForbiddenColor
            ext (by simpa using hattachment.symm)).elim
        · simpa only [restoredRootHostAttachment_firstForeignCoordinate] using
            (firstForeignLabels_hostIndependent skeleton
              (threeFiveEquiv (.inl (.inr first)))
              (Finset.mem_image.mpr ⟨first, by simp, rfl⟩)
              (threeFiveEquiv (.inl (.inr first')))
              (Finset.mem_image.mpr ⟨first', by simp, rfl⟩) huv)
      · exact
        (firstForeignHostForbiddenColor_ne_secondForeignHostForbiddenColor
          ext (by simpa using hattachment)).elim
  · rcases cv with (right | second')
    · rcases right with (free' | first')
      · exact (freeHostForbiddenColor_ne_secondForeignHostForbiddenColor
          ext (by simpa using hattachment.symm)).elim
      · exact
        (firstForeignHostForbiddenColor_ne_secondForeignHostForbiddenColor
          ext (by simpa using hattachment.symm)).elim
    · simpa only [restoredRootHostAttachment_secondForeignCoordinate] using
        (secondForeignLabels_hostIndependent skeleton
          (threeFiveEquiv (.inr second))
          (Finset.mem_image.mpr ⟨second, by simp, rfl⟩)
          (threeFiveEquiv (.inr second'))
          (Finset.mem_image.mpr ⟨second', by simp, rfl⟩) huv)

/-- The same compatibility law after decoding to `ThreeColor`. -/
theorem restoredRootAttachment_compatible {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext)
    {u v : Fin 15} (huv : u ≠ v)
    (hattachment : restoredRootAttachment ext u =
      restoredRootAttachment ext v) :
    encodedNeighborhoodColoring skeleton u v ≠
      restoredRootAttachment ext u := by
  let cu := threeFiveEquiv.symm u
  let cv := threeFiveEquiv.symm v
  have hu : u = threeFiveEquiv cu :=
    (threeFiveEquiv.apply_symm_apply u).symm
  have hv : v = threeFiveEquiv cv :=
    (threeFiveEquiv.apply_symm_apply v).symm
  rw [hu, hv] at huv hattachment ⊢
  rcases cu with (left | second)
  · rcases left with (free | first)
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · simpa only [restoredRootAttachment_freeCoordinate] using
            (freeLabels_encodedIndependent skeleton
              (threeFiveEquiv (.inl (.inl free)))
              (Finset.mem_image.mpr ⟨free, by simp, rfl⟩)
              (threeFiveEquiv (.inl (.inl free')))
              (Finset.mem_image.mpr ⟨free', by simp, rfl⟩) huv)
        · exact (freeForbiddenColor_ne_firstForeignForbiddenColor
            ext (by simpa using hattachment)).elim
      · exact (freeForbiddenColor_ne_secondForeignForbiddenColor
          ext (by simpa using hattachment)).elim
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · exact (freeForbiddenColor_ne_firstForeignForbiddenColor
            ext (by simpa using hattachment.symm)).elim
        · simpa only [restoredRootAttachment_firstForeignCoordinate] using
            (firstForeignLabels_encodedIndependent skeleton
              (threeFiveEquiv (.inl (.inr first)))
              (Finset.mem_image.mpr ⟨first, by simp, rfl⟩)
              (threeFiveEquiv (.inl (.inr first')))
              (Finset.mem_image.mpr ⟨first', by simp, rfl⟩) huv)
      · exact
        (firstForeignForbiddenColor_ne_secondForeignForbiddenColor
          ext (by simpa using hattachment)).elim
  · rcases cv with (right | second')
    · rcases right with (free' | first')
      · exact (freeForbiddenColor_ne_secondForeignForbiddenColor
          ext (by simpa using hattachment.symm)).elim
      · exact
        (firstForeignForbiddenColor_ne_secondForeignForbiddenColor
          ext (by simpa using hattachment.symm)).elim
    · simpa only [restoredRootAttachment_secondForeignCoordinate] using
        (secondForeignLabels_encodedIndependent skeleton
          (threeFiveEquiv (.inr second))
          (Finset.mem_image.mpr ⟨second, by simp, rfl⟩)
          (threeFiveEquiv (.inr second'))
          (Finset.mem_image.mpr ⟨second', by simp, rfl⟩) huv)

/-! ## The restored host and decoded K16 colourings -/

/-- Put the restored global root at label `Fin.last 15`. -/
noncomputable def restoredRootHostK16 {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    EdgeColoring (Fin 16) (Fin 4) :=
  extendByLast (ownNeighborhoodHostColoring skeleton)
    (restoredRootHostAttachment ext) 0

theorem restoredRootHostK16_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    NoMonochromaticTriangle (restoredRootHostK16 skeleton) := by
  exact noMono_extendByLast
    (ownNeighborhoodHostColoring skeleton)
    (ownNeighborhoodHostColoring_noMono skeleton)
    (restoredRootHostAttachment ext) 0
    (fun _ _ huv hattachment =>
      restoredRootHostAttachment_compatible skeleton huv hattachment)

theorem restoredRootHostAttachment_ne_own {kind : Kind}
    (ext : FiveSupportExtension kind) (i : Fin 15) :
    restoredRootHostAttachment ext i ≠ blockRootColor ext.block := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · simpa using freeHostForbiddenColor_ne_own ext
    · simpa using firstForeignHostForbiddenColor_ne_own ext
  · simpa using secondForeignHostForbiddenColor_ne_own ext

theorem restoredRootHostK16_avoids_own {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext)
    (u v : Fin 16) (huv : u ≠ v) :
    restoredRootHostK16 skeleton u v ≠ blockRootColor ext.block := by
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast j =>
          change extendByLast (ownNeighborhoodHostColoring skeleton)
              (restoredRootHostAttachment ext) 0 (Fin.last 15) j.castSucc ≠ _
          rw [extendByLast_last_old]
          exact restoredRootHostAttachment_ne_own ext j
  | cast i =>
      induction v using Fin.lastCases with
      | last =>
          change extendByLast (ownNeighborhoodHostColoring skeleton)
              (restoredRootHostAttachment ext) 0 i.castSucc (Fin.last 15) ≠ _
          rw [extendByLast_old_last]
          exact restoredRootHostAttachment_ne_own ext i
      | cast j =>
          change extendByLast (ownNeighborhoodHostColoring skeleton)
              (restoredRootHostAttachment ext) 0 i.castSucc j.castSucc ≠ _
          rw [extendByLast_old_old]
          apply ownNeighborhoodHostColoring_avoids_own skeleton i j
          intro hij
          apply huv
          simp [hij]

/-- The three-colour `K16` obtained by deleting the selected endpoint's own
host colour and restoring the global root as the last vertex. -/
noncomputable def restoredRootDecodedK16 {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    EdgeColoring (Fin 16) ThreeColor :=
  extendByLast (encodedNeighborhoodColoring skeleton)
    (restoredRootAttachment ext) 0

theorem restoredRootDecodedK16_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    NoMonochromaticTriangle (restoredRootDecodedK16 skeleton) := by
  exact noMono_extendByLast
    (encodedNeighborhoodColoring skeleton)
    (encodedNeighborhoodColoring_noMono skeleton)
    (restoredRootAttachment ext) 0
    (fun _ _ huv hattachment =>
      restoredRootAttachment_compatible skeleton huv hattachment)

/-- Rigidity of the restored root: its row is exactly the unique
deficient-colour attachment of the critical `K15`. -/
theorem restoredRootAttachment_eq_deficientColor15 {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    restoredRootAttachment ext =
      deficientColor15 (encodedNeighborhoodColoring skeleton)
        (encodedNeighborhoodColoring_noMono skeleton) := by
  exact attachment_eq_deficientColor15
    (encodedNeighborhoodColoring skeleton)
    (encodedNeighborhoodColoring_noMono skeleton)
    (restoredRootAttachment ext) 0
    (restoredRootDecodedK16_noMono skeleton)

/-- Consequently the restored root gives the canonical checked `15 -> 16`
extension, including the deliberately fixed diagonal value. -/
theorem restoredRootDecodedK16_eq_extendCriticalK15 {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    restoredRootDecodedK16 skeleton =
      extendCriticalK15 (encodedNeighborhoodColoring skeleton)
        (encodedNeighborhoodColoring_noMono skeleton) := by
  unfold restoredRootDecodedK16 extendCriticalK15
  rw [restoredRootAttachment_eq_deficientColor15 skeleton]

theorem restoredRootDecodedK16_eq_decodeHost_offDiagonal {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext)
    (u v : Fin 16) (huv : u ≠ v) :
    restoredRootDecodedK16 skeleton u v =
      decodeNonBlockColor (blockRootColor ext.block)
        (restoredRootHostK16 skeleton u v) := by
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast j =>
          change extendByLast (encodedNeighborhoodColoring skeleton)
              (restoredRootAttachment ext) 0 (Fin.last 15) j.castSucc =
            decodeNonBlockColor (blockRootColor ext.block)
              (extendByLast (ownNeighborhoodHostColoring skeleton)
                (restoredRootHostAttachment ext) 0 (Fin.last 15) j.castSucc)
          rw [extendByLast_last_old, extendByLast_last_old]
          rfl
  | cast i =>
      induction v using Fin.lastCases with
      | last =>
          change extendByLast (encodedNeighborhoodColoring skeleton)
              (restoredRootAttachment ext) 0 i.castSucc (Fin.last 15) =
            decodeNonBlockColor (blockRootColor ext.block)
              (extendByLast (ownNeighborhoodHostColoring skeleton)
                (restoredRootHostAttachment ext) 0 i.castSucc (Fin.last 15))
          rw [extendByLast_old_last, extendByLast_old_last]
          rfl
      | cast j => simp [restoredRootDecodedK16, restoredRootHostK16,
          encodedNeighborhoodColoring, decodeNonBlockColoring,
          ownNeighborhoodHostColoring]

theorem canonicalPalette_restoredRootDecodedK16 {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext)
    (u v : Fin 16) (huv : u ≠ v) :
    canonicalPalette (blockRootColor ext.block)
        (restoredRootDecodedK16 skeleton u v) =
      restoredRootHostK16 skeleton u v := by
  rw [restoredRootDecodedK16_eq_decodeHost_offDiagonal skeleton u v huv]
  exact canonicalPalette_decodeNonBlockColor
    (blockRootColor ext.block) (restoredRootHostK16 skeleton u v)
    (restoredRootHostK16_avoids_own skeleton u v huv)

/-! ## Checked K16 template type -/

theorem exists_weakEquiv_restoredRoot_k16Template {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    ∃ twisted : Bool, Nonempty
      (WeakColorEquiv (restoredRootDecodedK16 skeleton)
        (k16Template twisted)) := by
  obtain ⟨template, htemplate, ⟨equivalence⟩⟩ :=
    k16CriticalCatalogue_complete.2
      (restoredRootDecodedK16 skeleton)
      (restoredRootDecodedK16_noMono skeleton)
  simp [k16CriticalCatalogue] at htemplate
  rcases htemplate with rfl | rfl
  · exact ⟨false, ⟨by simpa [k16Template] using equivalence⟩⟩
  · exact ⟨true, ⟨by simpa [k16Template] using equivalence⟩⟩

/-! ## Alignment with the already catalogued K15 -/

/-- The canonical K15 partition is exactly the last vertex's three colour
neighbourhoods in the corresponding fixed K16 template. -/
theorem mem_canonicalPart_iff_lastColor
    (twisted : Bool) (q : ThreeColor) (x : Fin 15) :
    x ∈ canonicalPart twisted q ↔
      k16Template twisted (Fin.last 15) x.castSucc = q := by
  cases twisted <;> fin_cases q <;> fin_cases x <;> decide

/-- The partition normal form forces the transported restored-root row to
be the actual last-vertex row of the same K16 template type. -/
theorem catalogued_restoredRootAttachment_map_color {kind : Kind}
    {ext : FiveSupportExtension kind} {skeleton : DegreeTenSkeleton ext}
    (catalogued : CataloguedDegreeTenNeighborhood ext skeleton)
    (i : Fin 15) :
    catalogued.equivalence.colors (restoredRootAttachment ext i) =
      k16Template catalogued.twisted (Fin.last 15)
        (catalogued.equivalence.vertex i).castSucc := by
  have hcanonical := catalogued_supports_eq_canonical catalogued
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · rw [restoredRootAttachment_freeCoordinate]
      have hsource : threeFiveEquiv (.inl (.inl free)) ∈ freeLabels :=
        Finset.mem_image.mpr ⟨free, by simp, rfl⟩
      have himage : catalogued.equivalence.vertex
          (threeFiveEquiv (.inl (.inl free))) ∈
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors (freeForbiddenColor ext)) := by
        rw [← hcanonical.1]
        exact Finset.mem_image.mpr ⟨_, hsource, rfl⟩
      exact (mem_canonicalPart_iff_lastColor _ _ _).mp himage |>.symm
    · rw [restoredRootAttachment_firstForeignCoordinate]
      have hsource : threeFiveEquiv (.inl (.inr first)) ∈
          firstForeignLabels :=
        Finset.mem_image.mpr ⟨first, by simp, rfl⟩
      have himage : catalogued.equivalence.vertex
          (threeFiveEquiv (.inl (.inr first))) ∈
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors
              (firstForeignForbiddenColor ext)) := by
        rw [← hcanonical.2.1]
        exact Finset.mem_image.mpr ⟨_, hsource, rfl⟩
      exact (mem_canonicalPart_iff_lastColor _ _ _).mp himage |>.symm
  · rw [restoredRootAttachment_secondForeignCoordinate]
    have hsource : threeFiveEquiv (.inr second) ∈ secondForeignLabels :=
      Finset.mem_image.mpr ⟨second, by simp, rfl⟩
    have himage : catalogued.equivalence.vertex
        (threeFiveEquiv (.inr second)) ∈
        canonicalPart catalogued.twisted
          (catalogued.equivalence.colors
            (secondForeignForbiddenColor ext)) := by
      rw [← hcanonical.2.2]
      exact Finset.mem_image.mpr ⟨_, hsource, rfl⟩
    exact (mem_canonicalPart_iff_lastColor _ _ _).mp himage |>.symm

/-- Extend a permutation of `Fin 15` by fixing the last point of `Fin 16`. -/
noncomputable def liftLastEquiv (vertex : Fin 15 ≃ Fin 15) :
    Fin 16 ≃ Fin 16 where
  toFun := Fin.lastCases (Fin.last 15)
    (fun i => (vertex i).castSucc)
  invFun := Fin.lastCases (Fin.last 15)
    (fun i => (vertex.symm i).castSucc)
  left_inv := by
    intro x
    induction x using Fin.lastCases with
    | last => rfl
    | cast i => simp
  right_inv := by
    intro x
    induction x using Fin.lastCases with
    | last => rfl
    | cast i => simp

@[simp] theorem liftLastEquiv_last (vertex : Fin 15 ≃ Fin 15) :
    liftLastEquiv vertex (Fin.last 15) = Fin.last 15 := by
  rfl

@[simp] theorem liftLastEquiv_castSucc (vertex : Fin 15 ≃ Fin 15)
    (i : Fin 15) :
    liftLastEquiv vertex i.castSucc = (vertex i).castSucc := by
  simp [liftLastEquiv]

/-- The K15 catalogue equivalence extends over the restored root, with the
same critical type and the same colour permutation. -/
noncomputable def cataloguedRestoredRootWeakEquiv {kind : Kind}
    {ext : FiveSupportExtension kind} {skeleton : DegreeTenSkeleton ext}
    (catalogued : CataloguedDegreeTenNeighborhood ext skeleton) :
    WeakColorEquiv (restoredRootDecodedK16 skeleton)
      (k16Template catalogued.twisted) where
  vertex := liftLastEquiv catalogued.equivalence.vertex
  colors := catalogued.equivalence.colors
  map_color := by
    intro u v huv
    induction u using Fin.lastCases with
    | last =>
        induction v using Fin.lastCases with
        | last => exact (huv rfl).elim
        | cast j =>
            change catalogued.equivalence.colors
                (extendByLast (encodedNeighborhoodColoring skeleton)
                  (restoredRootAttachment ext) 0
                  (Fin.last 15) j.castSucc) = _
            rw [extendByLast_last_old]
            rw [liftLastEquiv_last, liftLastEquiv_castSucc]
            exact catalogued_restoredRootAttachment_map_color catalogued j
    | cast i =>
        induction v using Fin.lastCases with
        | last =>
            change catalogued.equivalence.colors
                (extendByLast (encodedNeighborhoodColoring skeleton)
                  (restoredRootAttachment ext) 0
                  i.castSucc (Fin.last 15)) = _
            rw [extendByLast_old_last]
            rw [liftLastEquiv_castSucc, liftLastEquiv_last]
            rw [(k16Template catalogued.twisted).color_symm]
            exact catalogued_restoredRootAttachment_map_color catalogued i
        | cast j =>
            have hij : i ≠ j := by
              intro h
              apply huv
              simp [h]
            change catalogued.equivalence.colors
                (extendByLast (encodedNeighborhoodColoring skeleton)
                  (restoredRootAttachment ext) 0 i.castSucc j.castSucc) = _
            rw [extendByLast_old_old]
            rw [liftLastEquiv_castSucc, liftLastEquiv_castSucc]
            calc
              catalogued.equivalence.colors
                  (encodedNeighborhoodColoring skeleton i j) =
                k15Template catalogued.twisted
                  (catalogued.equivalence.vertex i)
                  (catalogued.equivalence.vertex j) :=
                catalogued.equivalence.map_color i j hij
              _ = k16Template catalogued.twisted
                  (catalogued.equivalence.vertex i).castSucc
                  (catalogued.equivalence.vertex j).castSucc :=
                k15Template_edge_eq_k16Template _ _ _

/-- Finset form of the last-colour identity. -/
theorem liftK15Finset_canonicalPart_eq_colorNeighborhood
    (twisted : Bool) (q : ThreeColor) :
    liftK15Finset (canonicalPart twisted q) =
      colorNeighborhood (k16Template twisted) q (Fin.last 15) := by
  cases twisted <;> fin_cases q <;> decide

theorem catalogued_supports_eq_rootNeighborhoods {kind : Kind}
    {ext : FiveSupportExtension kind} {skeleton : DegreeTenSkeleton ext}
    (catalogued : CataloguedDegreeTenNeighborhood ext skeleton) :
    liftK15Finset
        (freeLabels.image catalogued.equivalence.vertex) =
        colorNeighborhood (k16Template catalogued.twisted)
          (catalogued.equivalence.colors (freeForbiddenColor ext))
          (Fin.last 15) ∧
      liftK15Finset
        (firstForeignLabels.image catalogued.equivalence.vertex) =
        colorNeighborhood (k16Template catalogued.twisted)
          (catalogued.equivalence.colors (firstForeignForbiddenColor ext))
          (Fin.last 15) ∧
      liftK15Finset
        (secondForeignLabels.image catalogued.equivalence.vertex) =
        colorNeighborhood (k16Template catalogued.twisted)
          (catalogued.equivalence.colors (secondForeignForbiddenColor ext))
          (Fin.last 15) := by
  have hcanonical := catalogued_supports_eq_canonical catalogued
  constructor
  · rw [hcanonical.1]
    exact liftK15Finset_canonicalPart_eq_colorNeighborhood _ _
  · constructor
    · rw [hcanonical.2.1]
      exact liftK15Finset_canonicalPart_eq_colorNeighborhood _ _
    · rw [hcanonical.2.2]
      exact liftK15Finset_canonicalPart_eq_colorNeighborhood _ _

/-- Existential aligned form: the same catalogue witness simultaneously
normalizes the K15 partition and the restored-root K16. -/
theorem exists_alignedRestoredRootK16 {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    ∃ catalogued : CataloguedDegreeTenNeighborhood ext skeleton,
      Nonempty (WeakColorEquiv (restoredRootDecodedK16 skeleton)
        (k16Template catalogued.twisted)) ∧
      freeLabels.image catalogued.equivalence.vertex =
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors (freeForbiddenColor ext)) ∧
        firstForeignLabels.image catalogued.equivalence.vertex =
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors
              (firstForeignForbiddenColor ext)) ∧
        secondForeignLabels.image catalogued.equivalence.vertex =
          canonicalPart catalogued.twisted
            (catalogued.equivalence.colors
              (secondForeignForbiddenColor ext)) := by
  obtain ⟨catalogued⟩ := exists_cataloguedDegreeTenNeighborhood skeleton
  have hcanonical := catalogued_supports_eq_canonical catalogued
  exact ⟨catalogued, ⟨cataloguedRestoredRootWeakEquiv catalogued⟩,
    hcanonical⟩

/-- Host-palette normal form with no residual colour relabelling.  The same
`twisted` bit supplied by the K15 partition classifies the restored K16, and
the selected endpoint's own host colour is exactly the omitted fourth
colour. -/
theorem exists_colorPreserving_hostK16Template_of_catalogued {kind : Kind}
    {ext : FiveSupportExtension kind} {skeleton : DegreeTenSkeleton ext}
    (catalogued : CataloguedDegreeTenNeighborhood ext skeleton) :
    ∃ vertex : Fin 16 ≃ Fin 16, ∀ u v, u ≠ v →
      restoredRootHostK16 skeleton (vertex u) (vertex v) =
        canonicalPalette (blockRootColor ext.block)
          (k16Template catalogued.twisted u v) := by
  let equivalence := cataloguedRestoredRootWeakEquiv catalogued
  obtain ⟨paletteVertex, hpalette⟩ :=
    k16Template_fullPaletteSymmetry
      catalogued.twisted equivalence.colors
  refine ⟨paletteVertex.trans equivalence.vertex.symm, ?_⟩
  intro u v huv
  have hsourceNe :
      (paletteVertex.trans equivalence.vertex.symm) u ≠
        (paletteVertex.trans equivalence.vertex.symm) v :=
    equivalence.vertex.symm.injective.ne
      (paletteVertex.injective.ne huv)
  have hdecoded :
      restoredRootDecodedK16 skeleton
          ((paletteVertex.trans equivalence.vertex.symm) u)
          ((paletteVertex.trans equivalence.vertex.symm) v) =
        k16Template catalogued.twisted u v := by
    apply equivalence.colors.injective
    calc
      equivalence.colors
          (restoredRootDecodedK16 skeleton
            ((paletteVertex.trans equivalence.vertex.symm) u)
            ((paletteVertex.trans equivalence.vertex.symm) v)) =
        k16Template catalogued.twisted
          (paletteVertex u) (paletteVertex v) := by
            simpa [equivalence] using equivalence.map_color
              (equivalence.vertex.symm (paletteVertex u))
              (equivalence.vertex.symm (paletteVertex v)) hsourceNe
      _ = equivalence.colors
          (k16Template catalogued.twisted u v) := hpalette u v huv
  calc
    restoredRootHostK16 skeleton
        ((paletteVertex.trans equivalence.vertex.symm) u)
        ((paletteVertex.trans equivalence.vertex.symm) v) =
      canonicalPalette (blockRootColor ext.block)
        (restoredRootDecodedK16 skeleton
          ((paletteVertex.trans equivalence.vertex.symm) u)
          ((paletteVertex.trans equivalence.vertex.symm) v)) :=
        (canonicalPalette_restoredRootDecodedK16 skeleton _ _ hsourceNe).symm
    _ = canonicalPalette (blockRootColor ext.block)
        (k16Template catalogued.twisted u v) :=
      congrArg (canonicalPalette (blockRootColor ext.block)) hdecoded

/-! ## The selected endpoint is a fourth-colour cone -/

/-- Add the selected endpoint after the restored-root K16, joining it
uniformly in its own colour. -/
noncomputable def selectedEndpointConeK17 {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    EdgeColoring (Fin 17) (Fin 4) :=
  extendByLast (restoredRootHostK16 skeleton)
    (fun _ => blockRootColor ext.block) 0

/-- The complete local seventeen-vertex picture is triangle-free.  Hence
there is no contradiction at this stage: it is exactly a fourth-colour cone
over the rigid critical K16 identified above. -/
theorem selectedEndpointConeK17_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : DegreeTenSkeleton ext) :
    NoMonochromaticTriangle (selectedEndpointConeK17 skeleton) := by
  exact noMono_extendByLast
    (restoredRootHostK16 skeleton)
    (restoredRootHostK16_noMono skeleton)
    (fun _ => blockRootColor ext.block) 0
    (fun _ _ huv _ => restoredRootHostK16_avoids_own skeleton _ _ huv)

#print axioms restoredRootHostK16_noMono
#print axioms restoredRootAttachment_eq_deficientColor15
#print axioms restoredRootDecodedK16_eq_extendCriticalK15
#print axioms cataloguedRestoredRootWeakEquiv
#print axioms catalogued_supports_eq_rootNeighborhoods
#print axioms exists_colorPreserving_hostK16Template_of_catalogued
#print axioms selectedEndpointConeK17_noMono

end ProfileDDegreeTenRestoredRootK16
end R4333
