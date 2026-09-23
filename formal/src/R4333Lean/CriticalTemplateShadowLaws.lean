import R4333Lean.K16ZeroIndependentClassification
import R4333Lean.CriticalTemplatePaletteSymmetry

/-!
# Maximum-independent-set shadow laws for the critical templates

The finite theorems in this file expose the rigid fact behind the useful
"shadow vertex" extension formulation.  In either critical `K16` template,
every independent five-set in one color is the neighborhood of a unique
vertex.  Moreover, maximum sets in two distinct colors are disjoint exactly
when their shadow vertices agree.

All four statements are checked by ordinary kernel reduction (`decide`), not
by `native_decide` or an external solver.
-/

namespace R4333

/-- A finite vertex set containing no edge of the selected color. -/
def IsColorIndependentSet {V C : Type*} [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (q : C) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y ≠ q

/-- Number of ordered distinct pairs in `S` whose edge has color `q`.  Using
a natural-valued checker makes exhaustive quantification over all finite sets
computable by ordinary kernel reduction. -/
def colorViolationCount {V C : Type*} [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (q : C) (S : Finset V) : Nat :=
  ((S ×ˢ S).filter fun pair =>
    pair.1 ≠ pair.2 ∧ c pair.1 pair.2 = q).card

theorem colorViolationCount_eq_zero_iff
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (q : C) (S : Finset V) :
    colorViolationCount c q S = 0 ↔ IsColorIndependentSet c q S := by
  simp [colorViolationCount, IsColorIndependentSet, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  aesop

def k16ShadowCount (twisted : Bool) (q : ThreeColor)
    (S : Finset (Fin 16)) : Nat :=
  (Finset.univ.filter fun shadow =>
    S = colorNeighborhood (k16Template twisted) q shadow).card

/-- The ten possible companions of the last vertex in an independent set of
the selected color. -/
def k16LastColorNonneighbors (twisted : Bool) (q : ThreeColor) :
    Finset (Fin 16) :=
  Finset.univ.filter fun x =>
    x ≠ Fin.last 15 ∧ k16Template twisted (Fin.last 15) x ≠ q

/-- The ten labels that can accompany `15` in a color-zero independent
five-set of the untwisted template. -/
def k16ZeroCandidateVertex : Fin 10 → Fin 16 :=
  ![1, 2, 4, 6, 8, 9, 10, 11, 12, 13]

theorem k16ZeroCandidateVertex_injective :
    Function.Injective k16ZeroCandidateVertex := by
  decide

theorem k16ZeroCandidateVertex_range :
    Finset.univ.image k16ZeroCandidateVertex =
      k16LastColorNonneighbors false 0 := by
  decide

theorem k16ZeroCandidateForbidden_iff : ∀ i j : Fin 10, i ≠ j → (
    k16ZeroCandidateForbidden i j = true ↔
      k16Untwisted (k16ZeroCandidateVertex i)
        (k16ZeroCandidateVertex j) = 0) := by
  decide

/- After a color-preserving automorphism sends one chosen set vertex to the
last label, the single color-zero audit is reduced to the five patterns
classified in `K16ZeroIndependentClassification`.  Palette symmetry and the
fact that the twist fixes color zero transport this one audit to all six
template/color pairs below. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16Untwisted_normalizedColorZero_shadowCount_eq_one :
    ∀ rest ∈ (k16LastColorNonneighbors false 0).powersetCard 4,
      colorViolationCount k16Untwisted 0
          (insert (Fin.last 15) rest) = 0 →
        k16ShadowCount false 0 (insert (Fin.last 15) rest) = 1 := by
  intro rest hrest hind
  let pulled : Finset (Fin 10) :=
    Finset.univ.filter fun i => k16ZeroCandidateVertex i ∈ rest
  have hrestSub : rest ⊆ k16LastColorNonneighbors false 0 :=
    (Finset.mem_powersetCard.mp hrest).1
  have himage : pulled.image k16ZeroCandidateVertex = rest := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      have hi' : k16ZeroCandidateVertex i ∈ rest :=
        (Finset.mem_filter.mp hi).2
      simpa [hix] using hi'
    · intro hx
      have hxrange : x ∈ Finset.univ.image k16ZeroCandidateVertex := by
        rw [k16ZeroCandidateVertex_range]
        exact hrestSub hx
      obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hxrange
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, hix⟩
      simpa [hix] using hx
  have hpulledCard : pulled.card = 4 := by
    have hc := congrArg Finset.card himage
    rw [Finset.card_image_of_injective _
      k16ZeroCandidateVertex_injective] at hc
    exact hc.trans (Finset.mem_powersetCard.mp hrest).2
  have hpulledMem :
      pulled ∈ (Finset.univ : Finset (Fin 10)).powersetCard 4 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hpulledCard⟩
  have hpulledInd : K16ZeroCandidateIndependent pulled := by
    intro i hi j hj hij
    by_contra hedge
    have hedgeTrue : k16ZeroCandidateForbidden i j = true :=
      Bool.eq_true_of_not_eq_false hedge
    have hiRest : k16ZeroCandidateVertex i ∈ rest :=
      (Finset.mem_filter.mp hi).2
    have hjRest : k16ZeroCandidateVertex j ∈ rest :=
      (Finset.mem_filter.mp hj).2
    have hiAll : k16ZeroCandidateVertex i ∈
        insert (Fin.last 15) rest := Finset.mem_insert_of_mem hiRest
    have hjAll : k16ZeroCandidateVertex j ∈
        insert (Fin.last 15) rest := Finset.mem_insert_of_mem hjRest
    have hcandNe : k16ZeroCandidateVertex i ≠
        k16ZeroCandidateVertex j :=
      k16ZeroCandidateVertex_injective.ne hij
    have hind' := (colorViolationCount_eq_zero_iff _ _ _).mp hind
    exact hind' (k16ZeroCandidateVertex i) hiAll
      (k16ZeroCandidateVertex j) hjAll hcandNe
      ((k16ZeroCandidateForbidden_iff (i := i) (j := j) hij).mp hedgeTrue)
  rcases k16ZeroCandidateIndependent_cardFour_classification
      pulled hpulledMem hpulledInd with h | h | h | h | h
  all_goals rw [← himage, h]
  all_goals decide

/-- The certified color-preserving automorphism maps a color-neighborhood to
the corresponding color-neighborhood. -/
theorem k16TemplateToLastEquiv_image_colorNeighborhood
    (twisted : Bool) (deleted : Fin 16) (q : ThreeColor) (shadow : Fin 16) :
    (colorNeighborhood (k16Template twisted) q shadow).image
        (k16TemplateToLastEquiv twisted deleted) =
      colorNeighborhood (k16Template twisted) q
        (k16TemplateToLastEquiv twisted deleted shadow) := by
  classical
  let e := k16TemplateToLastEquiv twisted deleted
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    subst y
    obtain ⟨hxs, hcolor⟩ :=
      (mem_colorNeighborhood _ _ _ _).mp hx
    apply (mem_colorNeighborhood _ _ _ _).mpr
    refine ⟨e.injective.ne hxs, ?_⟩
    calc
      k16Template twisted (e shadow) (e x) =
          k16Template twisted shadow x :=
        (k16TemplateToLastMap_preserves twisted deleted shadow x
          hxs.symm).symm
      _ = q := hcolor
  · intro hy
    let x := e.symm y
    have hey : e x = y := e.apply_symm_apply y
    obtain ⟨hyne, hcolor⟩ :=
      (mem_colorNeighborhood _ _ _ _).mp hy
    have hxs : x ≠ shadow := by
      intro h
      apply hyne
      rw [← hey, h]
    have hx : x ∈ colorNeighborhood (k16Template twisted) q shadow := by
      apply (mem_colorNeighborhood _ _ _ _).mpr
      refine ⟨hxs, ?_⟩
      calc
        k16Template twisted shadow x =
            k16Template twisted (e shadow) (e x) :=
          k16TemplateToLastMap_preserves twisted deleted shadow x hxs.symm
        _ = q := by simpa [e, hey] using hcolor
    exact Finset.mem_image.mpr ⟨x, hx, hey⟩

/-- Every color-zero maximum independent set of the untwisted K16 template
is the neighborhood of a unique shadow vertex. -/
theorem k16Untwisted_colorZero_maxIndependentSet_unique_shadow
    (S : Finset (Fin 16))
    (hcard : S.card = 5)
    (hindependent : IsColorIndependentSet k16Untwisted 0 S) :
    ∃! shadow : Fin 16,
      S = colorNeighborhood k16Untwisted 0 shadow := by
  classical
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨deleted, hdeleted⟩ := hSnonempty
  let e := k16TemplateToLastEquiv false deleted
  let mapped : Finset (Fin 16) := S.image e
  have hmappedCard : mapped.card = 5 := by
    simp only [mapped, Finset.card_image_of_injective _ e.injective]
    exact hcard
  have hlast : Fin.last 15 ∈ mapped := by
    apply Finset.mem_image.mpr
    refine ⟨deleted, hdeleted, ?_⟩
    exact k16TemplateToLastMap_deleted false deleted
  have hmappedIndependent :
      IsColorIndependentSet k16Untwisted 0 mapped := by
    intro x hx y hy hxy
    obtain ⟨x0, hx0, hxmap⟩ := Finset.mem_image.mp hx
    obtain ⟨y0, hy0, hymap⟩ := Finset.mem_image.mp hy
    have hx0y0 : x0 ≠ y0 := by
      intro h
      apply hxy
      rw [← hxmap, ← hymap, h]
    have hsource := hindependent x0 hx0 y0 hy0 hx0y0
    intro htarget
    apply hsource
    calc
      k16Untwisted x0 y0 = k16Untwisted (e x0) (e y0) :=
        k16TemplateToLastMap_preserves false deleted x0 y0 hx0y0
      _ = 0 := by simpa [hxmap, hymap] using htarget
  let rest := mapped.erase (Fin.last 15)
  have hrestSubset : rest ⊆ k16LastColorNonneighbors false 0 := by
    intro x hx
    obtain ⟨hxne, hxmapped⟩ := Finset.mem_erase.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, hxne, ?_⟩
    exact hmappedIndependent (Fin.last 15) hlast x hxmapped hxne.symm
  have hrestCard : rest.card = 4 := by
    simp only [rest, Finset.card_erase_of_mem hlast, hmappedCard]
  have hrestMem :
      rest ∈ (k16LastColorNonneighbors false 0).powersetCard 4 :=
    Finset.mem_powersetCard.mpr ⟨hrestSubset, hrestCard⟩
  have hinsert : insert (Fin.last 15) rest = mapped := by
    exact Finset.insert_erase hlast
  have hcount : k16ShadowCount false 0 mapped = 1 := by
    rw [← hinsert]
    apply k16Untwisted_normalizedColorZero_shadowCount_eq_one rest hrestMem
    apply (colorViolationCount_eq_zero_iff _ _ _).mpr
    rw [hinsert]
    exact hmappedIndependent
  rw [k16ShadowCount, Finset.card_eq_one] at hcount
  obtain ⟨mappedShadow, hfilter⟩ := hcount
  simp [k16Template] at hfilter
  have hmappedShadow : mapped =
      colorNeighborhood k16Untwisted 0 mappedShadow := by
    have : mappedShadow ∈ Finset.univ.filter fun x =>
        mapped = colorNeighborhood k16Untwisted 0 x := by
      rw [hfilter]
      simp
    simpa using (Finset.mem_filter.mp this).2
  let shadow := e.symm mappedShadow
  have hshadow : S = colorNeighborhood k16Untwisted 0 shadow := by
    apply Finset.image_injective e.injective
    calc
      S.image e = mapped := rfl
      _ = colorNeighborhood k16Untwisted 0 mappedShadow := hmappedShadow
      _ = colorNeighborhood k16Untwisted 0 (e shadow) := by
        simp [shadow]
      _ = (colorNeighborhood k16Untwisted 0 shadow).image e := by
        simpa [e, k16Template] using
          (k16TemplateToLastEquiv_image_colorNeighborhood
            false deleted 0 shadow).symm
  refine ⟨shadow, hshadow, ?_⟩
  intro other hother
  have hotherMapped : mapped =
      colorNeighborhood k16Untwisted 0 (e other) := by
    calc
      mapped = S.image e := rfl
      _ = (colorNeighborhood k16Untwisted 0 other).image e := by
        rw [hother]
      _ = colorNeighborhood k16Untwisted 0 (e other) := by
        simpa [e, k16Template] using
          k16TemplateToLastEquiv_image_colorNeighborhood
            false deleted 0 other
  have hotherMem : e other ∈ Finset.univ.filter fun x =>
      mapped = colorNeighborhood k16Untwisted 0 x := by
    simp [hotherMapped]
  rw [hfilter] at hotherMem
  have heq : e other = mappedShadow := by simpa using hotherMem
  apply e.injective
  simpa [shadow] using heq

/-- The sixteen-edge trade swaps only colors one and two, so its color-zero
graph is exactly the untwisted color-zero graph. -/
theorem k16Template_colorZero_iff : ∀ twisted : Bool, ∀ u v : Fin 16,
    k16Template twisted u v = 0 ↔ k16Untwisted u v = 0 := by
  intro twisted
  cases twisted <;> decide

theorem k16Template_colorZeroNeighborhood_eq
    (twisted : Bool) (shadow : Fin 16) :
    colorNeighborhood (k16Template twisted) 0 shadow =
      colorNeighborhood k16Untwisted 0 shadow := by
  ext x
  simp only [mem_colorNeighborhood]
  exact and_congr_right fun _ => k16Template_colorZero_iff twisted shadow x

theorem k16Template_colorZero_independent_iff
    (twisted : Bool) (S : Finset (Fin 16)) :
    IsColorIndependentSet (k16Template twisted) 0 S ↔
      IsColorIndependentSet k16Untwisted 0 S := by
  constructor
  · intro h x hx y hy hxy hcolor
    exact h x hx y hy hxy
      ((k16Template_colorZero_iff twisted x y).mpr hcolor)
  · intro h x hx y hy hxy hcolor
    exact h x hx y hy hxy
      ((k16Template_colorZero_iff twisted x y).mp hcolor)

theorem k16Template_colorZero_maxIndependentSet_unique_shadow
    (twisted : Bool) (S : Finset (Fin 16))
    (hcard : S.card = 5)
    (hindependent : IsColorIndependentSet (k16Template twisted) 0 S) :
    ∃! shadow : Fin 16,
      S = colorNeighborhood (k16Template twisted) 0 shadow := by
  have hbase := k16Untwisted_colorZero_maxIndependentSet_unique_shadow
    S hcard ((k16Template_colorZero_independent_iff twisted S).mp hindependent)
  simpa only [k16Template_colorZeroNeighborhood_eq twisted] using hbase

/-- A concrete palette permutation sending any selected label to zero. -/
def k16ColorToZeroCode : ThreeColor → Fin 6 := ![0, 2, 5]

theorem k16ColorToZeroCode_apply (q : ThreeColor) :
    criticalPaletteColorMap (k16ColorToZeroCode q) q = 0 := by
  fin_cases q <;> decide

/-- Palette symmetries transport color neighborhoods equivariantly. -/
theorem k16PaletteVertexEquiv_image_colorNeighborhood
    (twisted : Bool) (code : Fin 6) (q : ThreeColor) (shadow : Fin 16) :
    (colorNeighborhood (k16Template twisted) q shadow).image
        (k16PaletteVertexEquiv twisted code) =
      colorNeighborhood (k16Template twisted)
        (criticalPaletteColorMap code q)
        (k16PaletteVertexEquiv twisted code shadow) := by
  classical
  let e := k16PaletteVertexEquiv twisted code
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    subst y
    obtain ⟨hxs, hcolor⟩ :=
      (mem_colorNeighborhood _ _ _ _).mp hx
    apply (mem_colorNeighborhood _ _ _ _).mpr
    refine ⟨e.injective.ne hxs, ?_⟩
    rw [k16PaletteVertexEquiv_apply,
      k16PaletteVertexEquiv_apply]
    exact (k16PaletteVertexMap_preserves twisted code shadow x hxs.symm).trans
      (congrArg (criticalPaletteColorMap code) hcolor)
  · intro hy
    let x := e.symm y
    have hey : e x = y := e.apply_symm_apply y
    obtain ⟨hyne, hcolor⟩ :=
      (mem_colorNeighborhood _ _ _ _).mp hy
    have hxs : x ≠ shadow := by
      intro h
      apply hyne
      rw [← hey, h]
    have hsourceColor : k16Template twisted shadow x = q := by
      apply (criticalPaletteColorMap_bijective code).1
      calc
        criticalPaletteColorMap code (k16Template twisted shadow x) =
            k16Template twisted (e shadow) (e x) := by
          rw [k16PaletteVertexEquiv_apply,
            k16PaletteVertexEquiv_apply]
          exact (k16PaletteVertexMap_preserves
            twisted code shadow x hxs.symm).symm
        _ = criticalPaletteColorMap code q := by
          simpa [e, hey] using hcolor
    have hx : x ∈ colorNeighborhood (k16Template twisted) q shadow :=
      (mem_colorNeighborhood _ _ _ _).mpr ⟨hxs, hsourceColor⟩
    exact Finset.mem_image.mpr ⟨x, hx, hey⟩

/-- Every maximum independent set in either K16 template and any of its
three colors is the neighborhood of a unique shadow vertex.  The only finite
classification used is the single untwisted color-zero audit above. -/
theorem k16Template_maxIndependentSet_unique_shadow
    (twisted : Bool) (q : ThreeColor) (S : Finset (Fin 16))
    (hcard : S.card = 5)
    (hindependent : IsColorIndependentSet (k16Template twisted) q S) :
    ∃! shadow : Fin 16,
      S = colorNeighborhood (k16Template twisted) q shadow := by
  classical
  let code := k16ColorToZeroCode q
  let e := k16PaletteVertexEquiv twisted code
  let mapped := S.image e
  have hmappedCard : mapped.card = 5 := by
    simp only [mapped, Finset.card_image_of_injective _ e.injective]
    exact hcard
  have hmappedIndependent :
      IsColorIndependentSet (k16Template twisted) 0 mapped := by
    intro x hx y hy hxy
    obtain ⟨x0, hx0, hxmap⟩ := Finset.mem_image.mp hx
    obtain ⟨y0, hy0, hymap⟩ := Finset.mem_image.mp hy
    have hx0y0 : x0 ≠ y0 := by
      intro h
      apply hxy
      rw [← hxmap, ← hymap, h]
    have hsource := hindependent x0 hx0 y0 hy0 hx0y0
    intro htarget
    apply hsource
    apply (criticalPaletteColorMap_bijective code).1
    calc
      criticalPaletteColorMap code (k16Template twisted x0 y0) =
          k16Template twisted (e x0) (e y0) := by
        rw [k16PaletteVertexEquiv_apply,
          k16PaletteVertexEquiv_apply]
        exact (k16PaletteVertexMap_preserves
          twisted code x0 y0 hx0y0).symm
      _ = 0 := by simpa [hxmap, hymap] using htarget
      _ = criticalPaletteColorMap code q :=
        (k16ColorToZeroCode_apply q).symm
  obtain ⟨mappedShadow, hmappedShadow, hunique⟩ :=
    k16Template_colorZero_maxIndependentSet_unique_shadow
      twisted mapped hmappedCard hmappedIndependent
  let shadow := e.symm mappedShadow
  have hshadow :
      S = colorNeighborhood (k16Template twisted) q shadow := by
    apply Finset.image_injective e.injective
    calc
      S.image e = mapped := rfl
      _ = colorNeighborhood (k16Template twisted) 0 mappedShadow :=
        hmappedShadow
      _ = colorNeighborhood (k16Template twisted)
          (criticalPaletteColorMap code q) (e shadow) := by
        simp [shadow, k16ColorToZeroCode_apply q, code]
      _ = (colorNeighborhood (k16Template twisted) q shadow).image e := by
        simpa [e] using
          (k16PaletteVertexEquiv_image_colorNeighborhood
            twisted code q shadow).symm
  refine ⟨shadow, hshadow, ?_⟩
  intro other hother
  have hotherMapped : mapped =
      colorNeighborhood (k16Template twisted) 0 (e other) := by
    calc
      mapped = S.image e := rfl
      _ = (colorNeighborhood (k16Template twisted) q other).image e := by
        rw [hother]
      _ = colorNeighborhood (k16Template twisted)
          (criticalPaletteColorMap code q) (e other) := by
        simpa [e] using k16PaletteVertexEquiv_image_colorNeighborhood
          twisted code q other
      _ = colorNeighborhood (k16Template twisted) 0 (e other) := by
        simp [code, k16ColorToZeroCode_apply q]
  have heq : e other = mappedShadow := hunique (e other) hotherMapped
  apply e.injective
  simpa [shadow] using heq

/-- The restriction to labels `0,...,14` of a K16 color-neighborhood.  The
shadow may itself be the deleted vertex `15`. -/
def k15CompletionShadowNeighborhood (twisted : Bool) (q : ThreeColor)
    (shadow : Fin 16) : Finset (Fin 15) :=
  Finset.univ.filter fun x =>
    x.castSucc ≠ shadow ∧ k16Template twisted shadow x.castSucc = q

/- Distinct completion shadows cannot define the same visible maximum set. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15CompletionShadowNeighborhood_injective_of_card_five :
    ∀ twisted : Bool, ∀ q : ThreeColor, ∀ left right : Fin 16,
      (k15CompletionShadowNeighborhood twisted q left).card = 5 →
      (k15CompletionShadowNeighborhood twisted q right).card = 5 →
      k15CompletionShadowNeighborhood twisted q left =
        k15CompletionShadowNeighborhood twisted q right →
      left = right := by
  intro twisted q
  cases twisted <;> fin_cases q <;> decide

/-- In the untwisted template, neighborhoods in two distinct colors are
disjoint exactly when their centers agree. -/
theorem k16Untwisted_differentColorNeighborhood_disjoint_iff :
    ∀ q r : ThreeColor, q ≠ r → ∀ x y : Fin 16,
      Disjoint (colorNeighborhood k16Untwisted q x)
        (colorNeighborhood k16Untwisted r y) ↔ x = y := by
  decide

/-- In the twisted template, neighborhoods in two distinct colors are
disjoint exactly when their centers agree. -/
theorem k16Twisted_differentColorNeighborhood_disjoint_iff :
    ∀ q r : ThreeColor, q ≠ r → ∀ x y : Fin 16,
      Disjoint (colorNeighborhood k16Twisted q x)
        (colorNeighborhood k16Twisted r y) ↔ x = y := by
  decide

/-- For one color of the untwisted template, two different shadow
neighborhoods are disjoint exactly when their centers have that color. -/
theorem k16Untwisted_sameColorNeighborhood_disjoint_iff :
    ∀ q : ThreeColor, ∀ x y : Fin 16, x ≠ y →
      (Disjoint (colorNeighborhood k16Untwisted q x)
        (colorNeighborhood k16Untwisted q y) ↔ k16Untwisted x y = q) := by
  decide

/-- The same common-neighborhood law for the twisted template. -/
theorem k16Twisted_sameColorNeighborhood_disjoint_iff :
    ∀ q : ThreeColor, ∀ x y : Fin 16, x ≠ y →
      (Disjoint (colorNeighborhood k16Twisted q x)
        (colorNeighborhood k16Twisted q y) ↔ k16Twisted x y = q) := by
  decide

/-! ## Uniform K16 laws and semantic cross rows -/

theorem k16Template_differentColorNeighborhood_disjoint_iff
    (twisted : Bool) (q r : ThreeColor) (hqr : q ≠ r) (x y : Fin 16) :
    Disjoint (colorNeighborhood (k16Template twisted) q x)
      (colorNeighborhood (k16Template twisted) r y) ↔ x = y := by
  cases twisted
  · simpa [k16Template] using
      k16Untwisted_differentColorNeighborhood_disjoint_iff q r hqr x y
  · simpa [k16Template] using
      k16Twisted_differentColorNeighborhood_disjoint_iff q r hqr x y

theorem k16Template_sameColorNeighborhood_disjoint_iff
    (twisted : Bool) (q : ThreeColor) (x y : Fin 16) (hxy : x ≠ y) :
    Disjoint (colorNeighborhood (k16Template twisted) q x)
      (colorNeighborhood (k16Template twisted) q y) ↔
        k16Template twisted x y = q := by
  cases twisted
  · simpa [k16Template] using
      k16Untwisted_sameColorNeighborhood_disjoint_iff q x y hxy
  · simpa [k16Template] using
      k16Twisted_sameColorNeighborhood_disjoint_iff q x y hxy

/-- The positions of one label in a row from an outside vertex into a
critical K16 block.  `none` denotes the root/block color and `some r` the
three internal template colors. -/
def k16CrossRowSet (row : Fin 16 → Option ThreeColor)
    (label : Option ThreeColor) : Finset (Fin 16) :=
  Finset.univ.filter fun x => row x = label

def K16CrossRowCompatible (twisted : Bool)
    (row : Fin 16 → Option ThreeColor) : Prop :=
  ∀ r : ThreeColor,
    IsColorIndependentSet (k16Template twisted) r
      (k16CrossRowSet row (some r))

/-- Exact clone-row normal form. -/
def K16FullShadowRow (twisted : Bool) (row : Fin 16 → Option ThreeColor)
    (shadow : Fin 16) : Prop :=
  (∀ r : ThreeColor,
    k16CrossRowSet row (some r) =
      colorNeighborhood (k16Template twisted) r shadow) ∧
  k16CrossRowSet row none = {shadow}

theorem k16CrossRowSet_disjoint_of_ne
    (row : Fin 16 → Option ThreeColor) {left right : Option ThreeColor}
    (hne : left ≠ right) :
    Disjoint (k16CrossRowSet row left) (k16CrossRowSet row right) := by
  rw [Finset.disjoint_left]
  intro x hxleft hxright
  have hl : row x = left := (Finset.mem_filter.mp hxleft).2
  have hr : row x = right := (Finset.mem_filter.mp hxright).2
  exact hne (hl.symm.trans hr)

/-- If all three internal color classes of a compatible K16 cross row have
size five, the row is a unique clone row.  The singleton block-color class is
forced; it need not be assumed separately. -/
theorem k16CrossRow_unique_fullShadow
    (twisted : Bool) (row : Fin 16 → Option ThreeColor)
    (hcompatible : K16CrossRowCompatible twisted row)
    (hfive : ∀ r : ThreeColor,
      (k16CrossRowSet row (some r)).card = 5) :
    ∃! shadow : Fin 16, K16FullShadowRow twisted row shadow := by
  obtain ⟨s0, hs0, hus0⟩ :=
    k16Template_maxIndependentSet_unique_shadow twisted 0
      (k16CrossRowSet row (some 0)) (hfive 0) (hcompatible 0)
  obtain ⟨s1, hs1, hus1⟩ :=
    k16Template_maxIndependentSet_unique_shadow twisted 1
      (k16CrossRowSet row (some 1)) (hfive 1) (hcompatible 1)
  obtain ⟨s2, hs2, hus2⟩ :=
    k16Template_maxIndependentSet_unique_shadow twisted 2
      (k16CrossRowSet row (some 2)) (hfive 2) (hcompatible 2)
  have h01 : s0 = s1 := by
    apply (k16Template_differentColorNeighborhood_disjoint_iff
      twisted 0 1 (by decide) s0 s1).mp
    rw [← hs0, ← hs1]
    exact k16CrossRowSet_disjoint_of_ne row (by simp)
  have h02 : s0 = s2 := by
    apply (k16Template_differentColorNeighborhood_disjoint_iff
      twisted 0 2 (by decide) s0 s2).mp
    rw [← hs0, ← hs2]
    exact k16CrossRowSet_disjoint_of_ne row (by simp)
  subst s1
  subst s2
  have hinternal (r : ThreeColor) :
      k16CrossRowSet row (some r) =
        colorNeighborhood (k16Template twisted) r s0 := by
    fin_cases r
    · exact hs0
    · exact hs1
    · exact hs2
  have hnone : k16CrossRowSet row none = {s0} := by
    ext x
    simp only [k16CrossRowSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · intro hrow
      by_contra hxs
      let r : ThreeColor := k16Template twisted s0 x
      have hxNeighborhood :
          x ∈ colorNeighborhood (k16Template twisted) r s0 :=
        (mem_colorNeighborhood _ _ _ _).mpr ⟨hxs, rfl⟩
      have hxRow : x ∈ k16CrossRowSet row (some r) := by
        rw [hinternal r]
        exact hxNeighborhood
      have : row x = some r := (Finset.mem_filter.mp hxRow).2
      simp [hrow] at this
    · intro hxs
      subst x
      cases hrow : row s0 with
      | none => rfl
      | some r =>
          have hsRow : s0 ∈ k16CrossRowSet row (some r) := by
            simp [k16CrossRowSet, hrow]
          rw [hinternal r] at hsRow
          simp [colorNeighborhood] at hsRow
  refine ⟨s0, ⟨hinternal, hnone⟩, ?_⟩
  intro other hother
  exact hus0 other (hother.1 0)

theorem k16CrossRow_colorClass_card_sum
    (row : Fin 16 → Option ThreeColor) :
    (k16CrossRowSet row none).card +
      (k16CrossRowSet row (some 0)).card +
      (k16CrossRowSet row (some 1)).card +
      (k16CrossRowSet row (some 2)).card = 16 := by
  let sn := k16CrossRowSet row none
  let s0 := k16CrossRowSet row (some 0)
  let s1 := k16CrossRowSet row (some 1)
  let s2 := k16CrossRowSet row (some 2)
  have hn0 : Disjoint sn s0 :=
    k16CrossRowSet_disjoint_of_ne row (by simp)
  have hn1 : Disjoint sn s1 :=
    k16CrossRowSet_disjoint_of_ne row (by simp)
  have hn2 : Disjoint sn s2 :=
    k16CrossRowSet_disjoint_of_ne row (by simp)
  have h01 : Disjoint s0 s1 :=
    k16CrossRowSet_disjoint_of_ne row (by simp)
  have h02 : Disjoint s0 s2 :=
    k16CrossRowSet_disjoint_of_ne row (by simp)
  have h12 : Disjoint s1 s2 :=
    k16CrossRowSet_disjoint_of_ne row (by simp)
  have hunion : ((sn ∪ s0) ∪ s1) ∪ s2 = Finset.univ := by
    ext x
    cases hrow : row x with
    | none => simp [sn, s0, s1, s2, k16CrossRowSet, hrow]
    | some r =>
        fin_cases r
        · simp [sn, s0, s1, s2, k16CrossRowSet, hrow]
        · simp [sn, s0, s1, s2, k16CrossRowSet, hrow]
        · simp [sn, s0, s1, s2, k16CrossRowSet, hrow]
  have hdisj_n0_1 : Disjoint (sn ∪ s0) s1 :=
    Finset.disjoint_union_left.mpr ⟨hn1, h01⟩
  have hdisj_n01_2 : Disjoint ((sn ∪ s0) ∪ s1) s2 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hn2, h02⟩, h12⟩
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj_n01_2,
    Finset.card_union_of_disjoint hdisj_n0_1,
    Finset.card_union_of_disjoint hn0] at hcard
  simpa [sn, s0, s1, s2, Nat.add_assoc] using hcard

/-- Semantic entrance used by the star CNF: block-color count at most one is
equivalent to the `(5,5,5,1)` clone situation, hence selects one unique
shadow. -/
theorem k16CrossRow_of_blockColor_card_le_one_unique_fullShadow
    (twisted : Bool) (row : Fin 16 → Option ThreeColor)
    (hcompatible : K16CrossRowCompatible twisted row)
    (hblock : (k16CrossRowSet row none).card ≤ 1) :
    ∃! shadow : Fin 16, K16FullShadowRow twisted row shadow := by
  have hgood : NoMonochromaticTriangle (k16Template twisted) := by
    cases twisted <;> simp [k16Template, k16Untwisted_good, k16Twisted_good]
  have hcap (r : ThreeColor) :
      (k16CrossRowSet row (some r)).card ≤ 5 :=
    threeColor_independent_card_le_five_at_16
      (k16Template twisted) hgood r _ (hcompatible r)
  have hsum := k16CrossRow_colorClass_card_sum row
  have hfive : ∀ r : ThreeColor,
      (k16CrossRowSet row (some r)).card = 5 := by
    have h0 := hcap 0
    have h1 := hcap 1
    have h2 := hcap 2
    have hz : (k16CrossRowSet row (some 0)).card = 5 := by omega
    have ho : (k16CrossRowSet row (some 1)).card = 5 := by omega
    have ht : (k16CrossRowSet row (some 2)).card = 5 := by omega
    intro r
    fin_cases r
    · exact hz
    · exact ho
    · exact ht
  exact k16CrossRow_unique_fullShadow twisted row hcompatible hfive

/-- Two clone rows that can be joined by any triangle-safe edge have
different shadows.  For an internal-colored edge, the source edge between
the shadows is forced to have that same template color. -/
theorem k16FullShadowRows_edge_restriction
    (twisted : Bool) (left right : Fin 16 → Option ThreeColor)
    (leftShadow rightShadow : Fin 16)
    (hleft : K16FullShadowRow twisted left leftShadow)
    (hright : K16FullShadowRow twisted right rightShadow)
    (edge : Option ThreeColor)
    (hedge : Disjoint (k16CrossRowSet left edge)
      (k16CrossRowSet right edge)) :
    leftShadow ≠ rightShadow ∧
      ∀ r : ThreeColor, edge = some r →
        k16Template twisted leftShadow rightShadow = r := by
  have hne : leftShadow ≠ rightShadow := by
    intro heq
    subst rightShadow
    cases edge with
    | none =>
        rw [hleft.2, hright.2] at hedge
        simp at hedge
    | some r =>
        rw [hleft.1 r, hright.1 r] at hedge
        have hnonempty :
            (colorNeighborhood (k16Template twisted) r leftShadow).Nonempty := by
          have hdegree :
              (colorNeighborhood (k16Template twisted) r leftShadow).card = 5 := by
            change colorDegree (k16Template twisted) r leftShadow = 5
            cases twisted <;>
              exact threeColor_degree_eq_five_at_16 _
                (by simp [k16Template, k16Untwisted_good, k16Twisted_good]) r leftShadow
          exact Finset.nonempty_iff_ne_empty.mpr fun hempty => by
            rw [hempty] at hdegree
            simp at hdegree
        exact (Finset.nonempty_iff_ne_empty.mp hnonempty)
          ((Finset.disjoint_self_iff_empty _).mp hedge)
  refine ⟨hne, ?_⟩
  intro r hedgeColor
  subst edge
  rw [hleft.1 r, hright.1 r] at hedge
  exact (k16Template_sameColorNeighborhood_disjoint_iff
    twisted r leftShadow rightShadow hne).mp hedge

#print axioms R4333.k16Untwisted_normalizedColorZero_shadowCount_eq_one
#print axioms R4333.k16Template_maxIndependentSet_unique_shadow
#print axioms R4333.k15CompletionShadowNeighborhood_injective_of_card_five
#print axioms R4333.k16Untwisted_differentColorNeighborhood_disjoint_iff
#print axioms R4333.k16Twisted_differentColorNeighborhood_disjoint_iff
#print axioms R4333.k16Untwisted_sameColorNeighborhood_disjoint_iff
#print axioms R4333.k16Twisted_sameColorNeighborhood_disjoint_iff
#print axioms R4333.k16CrossRow_unique_fullShadow
#print axioms R4333.k16CrossRow_of_blockColor_card_le_one_unique_fullShadow
#print axioms R4333.k16FullShadowRows_edge_restriction

end R4333
