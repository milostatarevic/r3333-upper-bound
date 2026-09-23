import R4333Lean.SingleRootStarReduction61
import R4333Lean.SingleRootStarCNF

/-!
# Semantic entrance to the exact single-root star CNFs

This file bridges the semantic `SingleRootStarReduction61` to the four
`SingleRootStarCNF.CanonicalStarWitness` branches.  It is separate from the
frozen CNF generator and its byte-identity audit.
-/

namespace R4333

open Finset
open SingleRootStarCNF

namespace SingleRootStarWitness61

def cnfProfile : SingleRootProfile61 → SingleRootStarCNF.Profile
  | .twelveSixteenSixteenSixteen => .p12_16_16_16
  | .thirteenFifteenSixteenSixteen => .p13_15_16_16
  | .fourteenFourteenSixteenSixteen => .p14_14_16_16
  | .fourteenFifteenFifteenSixteen => .p14_15_15_16

@[simp] theorem profileSizes_cnfProfile (profile : SingleRootProfile61) :
    SingleRootStarCNF.profileSizes (cnfProfile profile) =
      [singleRootProfileTuple profile |>.1,
       singleRootProfileTuple profile |>.2.1,
       singleRootProfileTuple profile |>.2.2.1,
       singleRootProfileTuple profile |>.2.2.2] := by
  cases profile <;> rfl

/-! ## The exact consecutive four-block coordinate system -/

abbrev BlockPosition (profile : SingleRootStarCNF.Profile) :=
  Σ block : Fin 4, Fin (blockSize profile block)

def explicitBlockSize : SingleRootStarCNF.Profile → Fin 4 → Nat
  | .p12_16_16_16, 0 => 12
  | .p12_16_16_16, _ => 16
  | .p13_15_16_16, 0 => 13
  | .p13_15_16_16, 1 => 15
  | .p13_15_16_16, _ => 16
  | .p14_14_16_16, 0 => 14
  | .p14_14_16_16, 1 => 14
  | .p14_14_16_16, _ => 16
  | .p14_15_15_16, 0 => 14
  | .p14_15_15_16, 1 => 15
  | .p14_15_15_16, 2 => 15
  | .p14_15_15_16, _ => 16

def explicitBlockStart : SingleRootStarCNF.Profile → Fin 4 → Nat
  | .p12_16_16_16, 0 => 0
  | .p12_16_16_16, 1 => 12
  | .p12_16_16_16, 2 => 28
  | .p12_16_16_16, _ => 44
  | .p13_15_16_16, 0 => 0
  | .p13_15_16_16, 1 => 13
  | .p13_15_16_16, 2 => 28
  | .p13_15_16_16, _ => 44
  | .p14_14_16_16, 0 => 0
  | .p14_14_16_16, 1 => 14
  | .p14_14_16_16, 2 => 28
  | .p14_14_16_16, _ => 44
  | .p14_15_15_16, 0 => 0
  | .p14_15_15_16, 1 => 14
  | .p14_15_15_16, 2 => 29
  | .p14_15_15_16, _ => 44

@[simp] theorem blockSize_eq_explicit
    (profile : SingleRootStarCNF.Profile) (block : Fin 4) :
    blockSize profile block = explicitBlockSize profile block := by
  cases profile <;> fin_cases block <;> decide

@[simp] theorem blockStart_eq_explicit
    (profile : SingleRootStarCNF.Profile) (block : Fin 4) :
    blockStart profile block = explicitBlockStart profile block := by
  cases profile <;> fin_cases block <;> decide

def blockPositionToFin (profile : SingleRootStarCNF.Profile) :
    BlockPosition profile → Fin 60 := fun position =>
  ⟨blockStart profile position.1 + position.2.val,
    blockStart_add_lt_sixty profile position.1 position.2.isLt⟩

theorem blockPositionToFin_injective (profile : SingleRootStarCNF.Profile) :
    Function.Injective (blockPositionToFin profile) := by
  rintro ⟨leftBlock, left⟩ ⟨rightBlock, right⟩ h
  have hval := congrArg Fin.val h
  change blockStart profile leftBlock + left.val =
    blockStart profile rightBlock + right.val at hval
  have hleftBound : left.val < explicitBlockSize profile leftBlock := by
    simpa only [blockSize_eq_explicit] using left.isLt
  have hrightBound : right.val < explicitBlockSize profile rightBlock := by
    simpa only [blockSize_eq_explicit] using right.isLt
  have hvalExplicit :
      explicitBlockStart profile leftBlock + left.val =
        explicitBlockStart profile rightBlock + right.val := by
    simpa only [blockStart_eq_explicit] using hval
  have hblock : leftBlock = rightBlock := by
    cases profile <;> fin_cases leftBlock <;> fin_cases rightBlock
    all_goals simp [explicitBlockStart] at hvalExplicit
    all_goals simp [explicitBlockSize] at hleftBound
    all_goals simp [explicitBlockSize] at hrightBound
    all_goals first | rfl | omega
  subst rightBlock
  have hlocal : left = right := by
    apply Fin.ext
    omega
  subst right
  rfl

theorem blockPosition_card (profile : SingleRootStarCNF.Profile) :
    Fintype.card (BlockPosition profile) = 60 := by
  cases profile <;> decide

theorem blockPositionToFin_bijective (profile : SingleRootStarCNF.Profile) :
    Function.Bijective (blockPositionToFin profile) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨blockPositionToFin_injective profile, by
      rw [blockPosition_card]
      simp⟩

/-- Split `0,...,59` into the four consecutive blocks. -/
noncomputable def blockPositionEquiv (profile : SingleRootStarCNF.Profile) :
    Fin 60 ≃ BlockPosition profile :=
  (Equiv.ofBijective (blockPositionToFin profile)
    (blockPositionToFin_bijective profile)).symm

theorem blockPositionEquiv_blockVertex
    (profile : SingleRootStarCNF.Profile) (block : Fin 4)
    (position : Nat) (hposition : position < blockSize profile block) :
    blockPositionEquiv profile (blockVertex profile block position) =
      ⟨block, ⟨position, hposition⟩⟩ := by
  let localPos : Fin (blockSize profile block) := ⟨position, hposition⟩
  have hvertex : blockVertex profile block position =
      blockPositionToFin profile ⟨block, localPos⟩ := by
    apply Fin.ext
    simpa [blockPositionToFin, localPos] using
      blockVertex_val profile block hposition
  rw [hvertex]
  exact (blockPositionEquiv profile).apply_symm_apply ⟨block, localPos⟩

/-! ## The canonical non-block colour palette -/

theorem canonicalPalette_ne_block (block : Fin 4) (q : Fin 3) :
    canonicalPalette block q ≠ block := by
  fin_cases block <;> fin_cases q <;> decide

theorem canonicalPalette_injective (block : Fin 4) :
    Function.Injective (canonicalPalette block) := by
  fin_cases block <;> decide

def canonicalNeighborhoodColorMap (block : Fin 4) (q : Fin 3) :
    NeighborhoodColor (singleRootFourColorEquivFin4.symm block) :=
  ⟨singleRootFourColorEquivFin4.symm (canonicalPalette block q), by
    intro h
    apply canonicalPalette_ne_block block q
    exact singleRootFourColorEquivFin4.symm.injective h⟩

theorem canonicalNeighborhoodColorMap_bijective (block : Fin 4) :
    Function.Bijective (canonicalNeighborhoodColorMap block) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro left right h
    apply canonicalPalette_injective block
    apply singleRootFourColorEquivFin4.symm.injective
    exact congrArg Subtype.val h
  · simp

noncomputable def canonicalNeighborhoodColorEquiv (block : Fin 4) :
    Fin 3 ≃ NeighborhoodColor
      (singleRootFourColorEquivFin4.symm block) :=
  Equiv.ofBijective (canonicalNeighborhoodColorMap block)
    (canonicalNeighborhoodColorMap_bijective block)

@[simp] theorem canonicalNeighborhoodColorEquiv_apply
    (block : Fin 4) (q : Fin 3) :
    canonicalNeighborhoodColorEquiv block q =
      canonicalNeighborhoodColorMap block q := rfl

/-! ## Reading the four semantic blocks -/

abbrev normalizedHost
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :=
  mapEdgeColors c data.palette

def indexedRootColor (block : Fin 4) : FourColor :=
  singleRootFourColorEquivFin4.symm block

theorem degree_eq_blockSize
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4) :
    colorDegree (normalizedHost data) (indexedRootColor block) data.root =
      blockSize (cnfProfile data.profile) block := by
  have hdegree := data.degreeProfile
  cases hprofile : data.profile <;> fin_cases block
  all_goals simp [fourColorDegreeTuple, singleRootProfileTuple, hprofile] at hdegree
  all_goals first
    | simpa [normalizedHost, indexedRootColor, cnfProfile, blockSize,
        profileSizes, hprofile] using hdegree.1
    | simpa [normalizedHost, indexedRootColor, cnfProfile, blockSize,
        profileSizes, hprofile] using hdegree.2.1
    | simpa [normalizedHost, indexedRootColor, cnfProfile, blockSize,
        profileSizes, hprofile] using hdegree.2.2.1
    | simpa [normalizedHost, indexedRootColor, cnfProfile, blockSize,
        profileSizes, hprofile] using hdegree.2.2.2

theorem active_of_critical
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block) :
    colorDegree (normalizedHost data) (indexedRootColor block) data.root = 15 ∨
      colorDegree (normalizedHost data) (indexedRootColor block) data.root = 16 := by
  rw [degree_eq_blockSize]
  exact hcritical

/-! ## Palette-normalized critical block equivalences -/

def criticalTemplateTwisted : CriticalTemplateKind → Bool
  | .fifteenUntwisted => false
  | .fifteenTwisted => true
  | .sixteenUntwisted => false
  | .sixteenTwisted => true

def criticalTemplateFinEquiv (kind : CriticalTemplateKind) :
    Fin (criticalTemplateOrder kind) ≃ CriticalTemplateVertex kind := by
  cases kind <;> exact Equiv.refl _

theorem criticalTemplate_fullPaletteSymmetry
    (kind : CriticalTemplateKind) (e : Fin 3 ≃ Fin 3) :
    ∃ vertex : CriticalTemplateVertex kind ≃ CriticalTemplateVertex kind,
      ∀ u v, u ≠ v →
        criticalTemplateColoring kind (vertex u) (vertex v) =
          e (criticalTemplateColoring kind u v) := by
  cases kind with
  | fifteenUntwisted =>
      change ∃ vertex : Fin 15 ≃ Fin 15, ∀ u v, u ≠ v →
        k15Untwisted (vertex u) (vertex v) = e (k15Untwisted u v)
      exact k15Template_fullPaletteSymmetry false e
  | fifteenTwisted =>
      change ∃ vertex : Fin 15 ≃ Fin 15, ∀ u v, u ≠ v →
        k15Twisted (vertex u) (vertex v) = e (k15Twisted u v)
      exact k15Template_fullPaletteSymmetry true e
  | sixteenUntwisted =>
      change ∃ vertex : Fin 16 ≃ Fin 16, ∀ u v, u ≠ v →
        k16Untwisted (vertex u) (vertex v) = e (k16Untwisted u v)
      exact k16Template_fullPaletteSymmetry false e
  | sixteenTwisted =>
      change ∃ vertex : Fin 16 ≃ Fin 16, ∀ u v, u ≠ v →
        k16Twisted (vertex u) (vertex v) = e (k16Twisted u v)
      exact k16Template_fullPaletteSymmetry true e

noncomputable def criticalPaletteVertexEquiv
    (kind : CriticalTemplateKind) (e : Fin 3 ≃ Fin 3) :
    CriticalTemplateVertex kind ≃ CriticalTemplateVertex kind :=
  Classical.choose (criticalTemplate_fullPaletteSymmetry kind e)

theorem criticalPaletteVertexEquiv_preserves
    (kind : CriticalTemplateKind) (e : Fin 3 ≃ Fin 3)
    (u v : CriticalTemplateVertex kind) (huv : u ≠ v) :
    criticalTemplateColoring kind
        (criticalPaletteVertexEquiv kind e u)
        (criticalPaletteVertexEquiv kind e v) =
      e (criticalTemplateColoring kind u v) :=
  Classical.choose_spec (criticalTemplate_fullPaletteSymmetry kind e) u v huv

noncomputable def criticalCompletion
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block) :
    SharedCriticalCompletion (normalizedHost data)
      (noMono_mapEdgeColors c data.palette hc)
      (indexedRootColor block) data.root :=
  data.activeCompletion (indexedRootColor block)
    (active_of_critical data block hcritical)

theorem criticalCompletion_order_eq_blockSize
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block) :
    criticalTemplateOrder (criticalCompletion data block hcritical).kind =
      blockSize (cnfProfile data.profile) block :=
  (criticalCompletion data block hcritical).degree_eq_order.symm.trans
    (degree_eq_blockSize data block)

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-- The fixed numeric labeling of any checked critical kind agrees exactly
with the template table used by the frozen CNF generator. -/
theorem criticalTemplateColoring_finEquiv
    (kind : CriticalTemplateKind) (size : Nat)
    (horder : criticalTemplateOrder kind = size)
    (u v : Fin size) :
    criticalTemplateColoring kind
        (criticalTemplateFinEquiv kind (finCongr horder.symm u))
        (criticalTemplateFinEquiv kind (finCongr horder.symm v)) =
      templateColor size (criticalTemplateTwisted kind) u.val v.val := by
  cases kind with
  | fifteenUntwisted =>
      simp [criticalTemplateOrder] at horder
      subst size
      have hu : u.val % 15 = u.val := Nat.mod_eq_of_lt u.isLt
      have hv : v.val % 15 = v.val := Nat.mod_eq_of_lt v.isLt
      simp only [criticalTemplateFinEquiv, criticalTemplateColoring,
        criticalTemplateTwisted, templateColor, k15Template, fin15, hu, hv,
        if_pos, Equiv.refl_apply]
      congr 2 <;> apply Fin.ext <;> rfl
  | fifteenTwisted =>
      simp [criticalTemplateOrder] at horder
      subst size
      have hu : u.val % 15 = u.val := Nat.mod_eq_of_lt u.isLt
      have hv : v.val % 15 = v.val := Nat.mod_eq_of_lt v.isLt
      simp only [criticalTemplateFinEquiv, criticalTemplateColoring,
        criticalTemplateTwisted, templateColor, k15Template, fin15, hu, hv,
        if_pos, Equiv.refl_apply]
      congr 2 <;> apply Fin.ext <;> rfl
  | sixteenUntwisted =>
      simp [criticalTemplateOrder] at horder
      subst size
      have hu : u.val % 16 = u.val := Nat.mod_eq_of_lt u.isLt
      have hv : v.val % 16 = v.val := Nat.mod_eq_of_lt v.isLt
      simp only [criticalTemplateFinEquiv, criticalTemplateColoring,
        criticalTemplateTwisted, templateColor, k16Template, fin16, hu, hv,
        if_false, Equiv.refl_apply]
      congr 2 <;> apply Fin.ext <;> rfl
  | sixteenTwisted =>
      simp [criticalTemplateOrder] at horder
      subst size
      have hu : u.val % 16 = u.val := Nat.mod_eq_of_lt u.isLt
      have hv : v.val % 16 = v.val := Nat.mod_eq_of_lt v.isLt
      simp only [criticalTemplateFinEquiv, criticalTemplateColoring,
        criticalTemplateTwisted, templateColor, k16Template, fin16, hu, hv,
        if_false, Equiv.refl_apply]
      congr 2 <;> apply Fin.ext <;> rfl

set_option linter.unusedSimpArgs true
set_option linter.unusedTactic true
set_option linter.unreachableTactic true

/-- The local labeling of a critical root-neighbourhood.  Its middle vertex
automorphism conjugates the completion's arbitrary three-colour palette to
the canonical non-block palette expected by the CNF. -/
noncomputable def canonicalCriticalBlockEquiv
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block) :
    Fin (blockSize (cnfProfile data.profile) block) ≃
      NeighborhoodVertex (normalizedHost data)
        (indexedRootColor block) data.root := by
  let completion := criticalCompletion data block hcritical
  let orderEquiv :
      Fin (blockSize (cnfProfile data.profile) block) ≃
        Fin (criticalTemplateOrder completion.kind) :=
    finCongr (criticalCompletion_order_eq_blockSize
      data block hcritical).symm
  let colorEquiv : Fin 3 ≃ Fin 3 :=
    (canonicalNeighborhoodColorEquiv block).trans completion.paletteEquiv
  exact orderEquiv |>.trans (criticalTemplateFinEquiv completion.kind) |>.trans
    (criticalPaletteVertexEquiv completion.kind colorEquiv) |>.trans
    completion.neighborEquiv.symm

@[simp] theorem canonicalCriticalBlockEquiv_apply
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block)
    (u : Fin (blockSize (cnfProfile data.profile) block)) :
    canonicalCriticalBlockEquiv data block hcritical u =
      (criticalCompletion data block hcritical).neighborEquiv.symm
        (criticalPaletteVertexEquiv
          (criticalCompletion data block hcritical).kind
          ((canonicalNeighborhoodColorEquiv block).trans
            (criticalCompletion data block hcritical).paletteEquiv)
          (criticalTemplateFinEquiv
            (criticalCompletion data block hcritical).kind
            (finCongr (criticalCompletion_order_eq_blockSize
              data block hcritical).symm u))) := rfl

noncomputable def criticalBlockTwisted
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block) : Bool :=
  criticalTemplateTwisted (criticalCompletion data block hcritical).kind

/-- After the canonical palette conjugation, every critical local block edge
has exactly the table colour used by `CanonicalStarWitness`. -/
theorem canonicalCriticalBlockEquiv_color
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block)
    (u v : Fin (blockSize (cnfProfile data.profile) block))
    (huv : u ≠ v) :
    singleRootFourColorEquivFin4
        (normalizedHost data
          (canonicalCriticalBlockEquiv data block hcritical u).val
          (canonicalCriticalBlockEquiv data block hcritical v).val) =
      canonicalPalette block
        (templateColor (blockSize (cnfProfile data.profile) block)
          (criticalBlockTwisted data block hcritical) u.val v.val) := by
  let completion := criticalCompletion data block hcritical
  let horder := criticalCompletion_order_eq_blockSize data block hcritical
  let baseU : CriticalTemplateVertex completion.kind :=
    criticalTemplateFinEquiv completion.kind (finCongr horder.symm u)
  let baseV : CriticalTemplateVertex completion.kind :=
    criticalTemplateFinEquiv completion.kind (finCongr horder.symm v)
  let colorEquiv : Fin 3 ≃ Fin 3 :=
    (canonicalNeighborhoodColorEquiv block).trans completion.paletteEquiv
  let vertexEquiv : CriticalTemplateVertex completion.kind ≃
      CriticalTemplateVertex completion.kind :=
    criticalPaletteVertexEquiv completion.kind colorEquiv
  let x : NeighborhoodVertex (normalizedHost data)
      (indexedRootColor block) data.root :=
    completion.neighborEquiv.symm (vertexEquiv baseU)
  let y : NeighborhoodVertex (normalizedHost data)
      (indexedRootColor block) data.root :=
    completion.neighborEquiv.symm (vertexEquiv baseV)
  have hbase : baseU ≠ baseV := by
    intro h
    apply huv
    apply (finCongr horder.symm).injective
    apply (criticalTemplateFinEquiv completion.kind).injective
    exact h
  have hxy : x ≠ y := by
    intro h
    apply hbase
    apply vertexEquiv.injective
    apply completion.neighborEquiv.symm.injective
    exact h
  have hpalette := criticalPaletteVertexEquiv_preserves
    completion.kind colorEquiv baseU baseV hbase
  have horiginal := completion.original_color_of_template_edge x y hxy
  have htemplate :
      criticalTemplateColoring completion.kind baseU baseV =
        templateColor (blockSize (cnfProfile data.profile) block)
          (criticalBlockTwisted data block hcritical) u.val v.val := by
    simpa [completion, horder, baseU, baseV, criticalBlockTwisted] using
      criticalTemplateColoring_finEquiv completion.kind
        (blockSize (cnfProfile data.profile) block) horder u v
  have hhost :
      normalizedHost data x.val y.val =
        (canonicalNeighborhoodColorEquiv block
          (criticalTemplateColoring completion.kind baseU baseV)).val := by
    calc
      normalizedHost data x.val y.val =
          ((completion.paletteEquiv.symm
            (criticalTemplateColoring completion.kind
              (completion.neighborEquiv x)
              (completion.neighborEquiv y)) :
            NeighborhoodColor (indexedRootColor block)) : FourColor) :=
        horiginal.symm
      _ = ((completion.paletteEquiv.symm
            (criticalTemplateColoring completion.kind
              (vertexEquiv baseU) (vertexEquiv baseV)) :
            NeighborhoodColor (indexedRootColor block)) : FourColor) := by
        simp [x, y]
      _ = ((completion.paletteEquiv.symm
            (colorEquiv
              (criticalTemplateColoring completion.kind baseU baseV)) :
            NeighborhoodColor (indexedRootColor block)) : FourColor) := by
        rw [hpalette]
      _ = (canonicalNeighborhoodColorEquiv block
            (criticalTemplateColoring completion.kind baseU baseV)).val := by
        simp only [colorEquiv, Equiv.trans_apply]
        exact congrArg Subtype.val
          (completion.paletteEquiv.symm_apply_apply
            (canonicalNeighborhoodColorEquiv block
              (criticalTemplateColoring completion.kind baseU baseV)))
  rw [show canonicalCriticalBlockEquiv data block hcritical u = x by
      simp [x, vertexEquiv, baseU, completion, colorEquiv]]
  rw [show canonicalCriticalBlockEquiv data block hcritical v = y by
      simp [y, vertexEquiv, baseV, completion, colorEquiv]]
  rw [hhost, htemplate]
  simp [canonicalNeighborhoodColorEquiv_apply,
    canonicalNeighborhoodColorMap]

/-! ## One local equivalence per block, then one global relabeling -/

noncomputable def blockLocalEquiv
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4) :
    Fin (blockSize (cnfProfile data.profile) block) ≃
      NeighborhoodVertex (normalizedHost data)
        (indexedRootColor block) data.root :=
  if hcritical : isCriticalBlock (cnfProfile data.profile) block then
    canonicalCriticalBlockEquiv data block hcritical
  else
    neighborhoodVertexEquivFinOfDegree
      (normalizedHost data) (indexedRootColor block) data.root
      (degree_eq_blockSize data block)

noncomputable def blockTwisted
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4) : Bool :=
  if hcritical : isCriticalBlock (cnfProfile data.profile) block then
    criticalBlockTwisted data block hcritical
  else false

theorem blockLocalEquiv_of_critical
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block) :
    blockLocalEquiv data block =
      canonicalCriticalBlockEquiv data block hcritical := by
  simp only [blockLocalEquiv, dif_pos hcritical]

theorem blockTwisted_of_critical
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block) :
    blockTwisted data block = criticalBlockTwisted data block hcritical := by
  simp only [blockTwisted, dif_pos hcritical]

abbrev BlockNeighborhood
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :=
  Σ block : Fin 4, NeighborhoodVertex (normalizedHost data)
    (indexedRootColor block) data.root

abbrev NonRoot
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :=
  {v : Fin 61 // v ≠ data.root}

noncomputable def blockPositionNeighborhoodEquiv
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    BlockPosition (cnfProfile data.profile) ≃ BlockNeighborhood data where
  toFun position := ⟨position.1, blockLocalEquiv data position.1 position.2⟩
  invFun position :=
    ⟨position.1, (blockLocalEquiv data position.1).symm position.2⟩
  left_inv := by
    rintro ⟨block, position⟩
    simp
  right_inv := by
    rintro ⟨block, vertex⟩
    simp

def blockNeighborhoodToNonRoot
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    BlockNeighborhood data → NonRoot data := fun position =>
  ⟨position.2.val,
    ((mem_colorNeighborhood (normalizedHost data)
      (indexedRootColor position.1) data.root position.2.val).mp
        position.2.property).1⟩

theorem blockNeighborhoodToNonRoot_injective
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    Function.Injective (blockNeighborhoodToNonRoot data) := by
  rintro ⟨leftBlock, left⟩ ⟨rightBlock, right⟩ h
  have hval : left.val = right.val := congrArg Subtype.val h
  have hleftColor :=
    ((mem_colorNeighborhood (normalizedHost data)
      (indexedRootColor leftBlock) data.root left.val).mp left.property).2
  have hrightColor :=
    ((mem_colorNeighborhood (normalizedHost data)
      (indexedRootColor rightBlock) data.root right.val).mp right.property).2
  have hcolor : indexedRootColor leftBlock = indexedRootColor rightBlock :=
    hleftColor.symm.trans (by simpa [hval] using hrightColor)
  have hblock : leftBlock = rightBlock := by
    apply singleRootFourColorEquivFin4.symm.injective
    exact hcolor
  subst rightBlock
  have hvertex : left = right := Subtype.ext hval
  subst right
  rfl

theorem blockNeighborhoodToNonRoot_surjective
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    Function.Surjective (blockNeighborhoodToNonRoot data) := by
  intro vertex
  let block : Fin 4 := singleRootFourColorEquivFin4
    (normalizedHost data data.root vertex.val)
  have hmember : vertex.val ∈ colorNeighborhood (normalizedHost data)
      (indexedRootColor block) data.root := by
    apply (mem_colorNeighborhood (normalizedHost data)
      (indexedRootColor block) data.root vertex.val).mpr
    constructor
    · exact vertex.property
    · simp [block, indexedRootColor]
  refine ⟨⟨block, ⟨vertex.val, hmember⟩⟩, ?_⟩
  apply Subtype.ext
  rfl

noncomputable def blockNeighborhoodNonRootEquiv
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    BlockNeighborhood data ≃ NonRoot data :=
  Equiv.ofBijective (blockNeighborhoodToNonRoot data)
    ⟨blockNeighborhoodToNonRoot_injective data,
      blockNeighborhoodToNonRoot_surjective data⟩

/-- The single global relabeling of all sixty non-root vertices. -/
noncomputable def hostRelabelEquiv
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) : Fin 60 ≃ NonRoot data :=
  (blockPositionEquiv (cnfProfile data.profile)).trans
    ((blockPositionNeighborhoodEquiv data).trans
      (blockNeighborhoodNonRootEquiv data))

theorem hostRelabelEquiv_blockVertex
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (position : Nat)
    (hposition : position < blockSize (cnfProfile data.profile) block) :
    hostRelabelEquiv data
        (blockVertex (cnfProfile data.profile) block position) =
      ⟨(blockLocalEquiv data block ⟨position, hposition⟩).val,
        ((mem_colorNeighborhood (normalizedHost data)
          (indexedRootColor block) data.root
          (blockLocalEquiv data block ⟨position, hposition⟩).val).mp
            (blockLocalEquiv data block ⟨position, hposition⟩).property).1⟩ := by
  simp [hostRelabelEquiv, blockNeighborhoodNonRootEquiv,
    blockNeighborhoodToNonRoot, blockPositionNeighborhoodEquiv,
    blockPositionEquiv_blockVertex _ block position hposition]

theorem hostRelabelEquiv_blockVertex_val
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (block : Fin 4)
    (position : Nat)
    (hposition : position < blockSize (cnfProfile data.profile) block) :
    (hostRelabelEquiv data
      (blockVertex (cnfProfile data.profile) block position)).val =
        (blockLocalEquiv data block ⟨position, hposition⟩).val :=
  congrArg Subtype.val
    (hostRelabelEquiv_blockVertex data block position hposition)

noncomputable def hostRelabelVertex
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) : Fin 60 → Fin 61 :=
  fun vertex ↦ (hostRelabelEquiv data vertex).val

theorem hostRelabelVertex_injective
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    Function.Injective (hostRelabelVertex data) := by
  intro left right h
  apply (hostRelabelEquiv data).injective
  apply Subtype.ext
  exact h

/-- Pull the normalized host coloring onto the exact consecutive `Fin 60`
coordinate system, then enumerate its four colors as `Fin 4`. -/
noncomputable def canonicalStarColoring
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    EdgeColoring (Fin 60) (Fin 4) :=
  mapEdgeColors
    (pullbackColoring (normalizedHost data) (hostRelabelVertex data))
    singleRootFourColorEquivFin4

@[simp] theorem canonicalStarColoring_apply
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) (left right : Fin 60) :
    canonicalStarColoring data left right =
      singleRootFourColorEquivFin4
        (normalizedHost data (hostRelabelVertex data left)
          (hostRelabelVertex data right)) := rfl

theorem canonicalStarColoring_noMono
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    NoMonochromaticTriangle (canonicalStarColoring data) :=
  noMono_mapEdgeColors _ singleRootFourColorEquivFin4
    (noMono_pullback (normalizedHost data) (hostRelabelVertex data)
      (hostRelabelVertex_injective data)
      (noMono_mapEdgeColors c data.palette hc))

theorem canonicalStarColoring_rootForbidden
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (block : Fin 4) (left right : Nat)
    (hleft : left < blockSize (cnfProfile data.profile) block)
    (hright : right < blockSize (cnfProfile data.profile) block)
    (hlr : left < right) :
    canonicalStarColoring data
        (blockVertex (cnfProfile data.profile) block left)
        (blockVertex (cnfProfile data.profile) block right) ≠ block := by
  let localLeft : Fin (blockSize (cnfProfile data.profile) block) :=
    ⟨left, hleft⟩
  let localRight : Fin (blockSize (cnfProfile data.profile) block) :=
    ⟨right, hright⟩
  let hostLeft := blockLocalEquiv data block localLeft
  let hostRight := blockLocalEquiv data block localRight
  have hlocal : localLeft ≠ localRight := by
    intro h
    have := congrArg Fin.val h
    simp [localLeft, localRight] at this
    omega
  have hhost : hostLeft.val ≠ hostRight.val := by
    intro h
    apply hlocal
    apply (blockLocalEquiv data block).injective
    apply Subtype.ext
    exact h
  have hnot := neighborhood_avoids_own_color
    (normalizedHost data) (noMono_mapEdgeColors c data.palette hc)
    hostLeft.property hostRight.property hhost
  rw [canonicalStarColoring_apply]
  rw [show hostRelabelVertex data
        (blockVertex (cnfProfile data.profile) block left) = hostLeft.val by
      exact hostRelabelEquiv_blockVertex_val data block left hleft]
  rw [show hostRelabelVertex data
        (blockVertex (cnfProfile data.profile) block right) = hostRight.val by
      exact hostRelabelEquiv_blockVertex_val data block right hright]
  intro hcolor
  apply hnot
  apply singleRootFourColorEquivFin4.injective
  simpa [indexedRootColor] using hcolor

theorem canonicalStarColoring_templateCanonical
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc)
    (block : Fin 4)
    (hcritical : isCriticalBlock (cnfProfile data.profile) block)
    (left right : Nat)
    (hleft : left < blockSize (cnfProfile data.profile) block)
    (hright : right < blockSize (cnfProfile data.profile) block)
    (hlr : left < right) :
    canonicalStarColoring data
        (blockVertex (cnfProfile data.profile) block left)
        (blockVertex (cnfProfile data.profile) block right) =
      canonicalPalette block
        (templateColor (blockSize (cnfProfile data.profile) block)
          (blockTwisted data block) left right) := by
  let localLeft : Fin (blockSize (cnfProfile data.profile) block) :=
    ⟨left, hleft⟩
  let localRight : Fin (blockSize (cnfProfile data.profile) block) :=
    ⟨right, hright⟩
  have hlocal : localLeft ≠ localRight := by
    intro h
    have := congrArg Fin.val h
    simp [localLeft, localRight] at this
    omega
  rw [canonicalStarColoring_apply]
  rw [show hostRelabelVertex data
        (blockVertex (cnfProfile data.profile) block left) =
          (blockLocalEquiv data block localLeft).val by
      exact hostRelabelEquiv_blockVertex_val data block left hleft]
  rw [show hostRelabelVertex data
        (blockVertex (cnfProfile data.profile) block right) =
          (blockLocalEquiv data block localRight).val by
      exact hostRelabelEquiv_blockVertex_val data block right hright]
  rw [blockLocalEquiv_of_critical data block hcritical]
  rw [blockTwisted_of_critical data block hcritical]
  simpa [localLeft, localRight] using
    canonicalCriticalBlockEquiv_color data block hcritical
      localLeft localRight hlocal

/-! ## The semantic cover theorem -/

/-- Every checked single-root reduction canonically yields a witness for the
matching frozen star-CNF profile. -/
noncomputable def canonicalStarWitnessOfReduction
    {c : EdgeColoring (Fin 61) FourColor}
    {hc : NoMonochromaticTriangle c}
    (data : SingleRootStarReduction61 c hc) :
    CanonicalStarWitness (cnfProfile data.profile) where
  coloring := canonicalStarColoring data
  noMono := canonicalStarColoring_noMono data
  chosenTemplate := blockTwisted data
  rootForbidden := canonicalStarColoring_rootForbidden data
  templateCanonical := canonicalStarColoring_templateCanonical data

/-- Complete semantic entrance to the four exact CNFs: any hypothetical good
four-coloring of `K61` supplies one of their canonical witnesses. -/
theorem exists_canonicalStarWitness61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ profile : SingleRootStarCNF.Profile,
      Nonempty (CanonicalStarWitness profile) := by
  obtain ⟨data⟩ := exists_singleRootStarReduction61 c hc
  exact ⟨cnfProfile data.profile,
    ⟨canonicalStarWitnessOfReduction data⟩⟩

/-- A statement in the exact shape consumed by the certificate-boundary
theorem in `SingleRootStarObstruction61`. -/
theorem singleRootStarCover61 :
    ∀ (c : EdgeColoring (Fin 61) FourColor),
      NoMonochromaticTriangle c →
        ∃ profile : SingleRootStarCNF.Profile,
          Nonempty (CanonicalStarWitness profile) :=
  exists_canonicalStarWitness61

#print axioms R4333.SingleRootStarWitness61.criticalTemplateColoring_finEquiv
#print axioms R4333.SingleRootStarWitness61.canonicalCriticalBlockEquiv_color
#print axioms R4333.SingleRootStarWitness61.hostRelabelEquiv
#print axioms R4333.SingleRootStarWitness61.canonicalStarWitnessOfReduction
#print axioms R4333.SingleRootStarWitness61.singleRootStarCover61

end SingleRootStarWitness61

end R4333
