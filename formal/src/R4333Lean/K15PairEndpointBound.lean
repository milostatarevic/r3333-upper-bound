import R4333Lean.CriticalTemplateMaximumSetIntersection

/-!
# A completion-shadow endpoint bound for two critical K15 blocks

The elementary row-cap argument gives only `75` endpoint-coloured edges in
a `15 x 15` cross matrix.  The deleted-vertex completion of a critical K15
improves this to `78`: a row saturated in both common colours determines one
of only six completion shadows, and no completion shadow can occur on three
source rows without making a monochromatic triangle in the source K15.

The theorem is stated for a normalized cross matrix.  `none` is the target
block colour, `some (palette wildcard)` is the source block colour, and the
two remaining `some` labels are the two colours common to both blocks.
-/

namespace R4333
namespace K15PairEndpointBound

open Finset

def otherColor0 : ThreeColor → ThreeColor := ![1, 0, 0]
def otherColor1 : ThreeColor → ThreeColor := ![2, 2, 1]

theorem otherColor0_ne (wildcard : ThreeColor) :
    otherColor0 wildcard ≠ wildcard := by
  fin_cases wildcard <;> decide

theorem otherColor1_ne (wildcard : ThreeColor) :
    otherColor1 wildcard ≠ wildcard := by
  fin_cases wildcard <;> decide

theorem otherColor0_ne_otherColor1 (wildcard : ThreeColor) :
    otherColor0 wildcard ≠ otherColor1 wildcard := by
  fin_cases wildcard <;> decide

theorem eq_otherColor_of_ne (wildcard q : ThreeColor)
    (hq : q ≠ wildcard) :
    q = otherColor0 wildcard ∨ q = otherColor1 wildcard := by
  fin_cases wildcard <;> fin_cases q <;>
    simp_all [otherColor0, otherColor1]

/-! ## Completion shadows of maximum sets in a deleted K16 -/

theorem k15Template_independent_card_le_five
    (twisted : Bool) (q : ThreeColor) (S : Finset (Fin 15))
    (hS : IsColorIndependentSet (k15Template twisted) q S) :
    S.card ≤ 5 := by
  have hgood : NoMonochromaticTriangle (k16Template twisted) := by
    cases twisted <;>
      simp [k16Template, k16Untwisted_good, k16Twisted_good]
  have hlift := threeColor_independent_card_le_five_at_16
    (k16Template twisted) hgood q (liftK15Finset S)
      (liftK15Finset_independent twisted q S hS)
  simpa using hlift

/-- Every independent five-set in the K15 deletion is the visible part of
one unique K16 neighbourhood. -/
theorem k15Template_maxIndependentSet_unique_completionShadow
    (twisted : Bool) (q : ThreeColor) (S : Finset (Fin 15))
    (hcard : S.card = 5)
    (hS : IsColorIndependentSet (k15Template twisted) q S) :
    ∃! shadow : Fin 16,
      S = k15CompletionShadowNeighborhood twisted q shadow := by
  have hliftCard : (liftK15Finset S).card = 5 := by simpa using hcard
  have hliftIndependent := liftK15Finset_independent twisted q S hS
  obtain ⟨shadow, hshadow, _⟩ :=
    k16Template_maxIndependentSet_unique_shadow twisted q
      (liftK15Finset S) hliftCard hliftIndependent
  have hvisible :
      S = k15CompletionShadowNeighborhood twisted q shadow := by
    ext x
    have hx := Finset.ext_iff.mp hshadow x.castSucc
    simpa [liftK15Finset, k15CompletionShadowNeighborhood,
      mem_colorNeighborhood] using hx
  refine ⟨shadow, hvisible, ?_⟩
  intro other hother
  symm
  apply k15CompletionShadowNeighborhood_injective_of_card_five
    twisted q shadow other
  · simpa [← hvisible] using hcard
  · simpa [← hother] using hcard
  · exact hvisible.symm.trans hother

/-- The six completion shadows on which maximum sets in two distinct
colours can simultaneously live. -/
def allowedCompletionShadows (twisted : Bool)
    (first second : ThreeColor) : Finset (Fin 16) :=
  Finset.univ.filter fun shadow =>
    (k15CompletionShadowNeighborhood twisted first shadow).card = 5 ∧
    (k15CompletionShadowNeighborhood twisted second shadow).card = 5

set_option maxRecDepth 100000 in
theorem allowedCompletionShadows_card
    (twisted : Bool) (first second : ThreeColor) (hne : first ≠ second) :
    (allowedCompletionShadows twisted first second).card = 6 := by
  cases twisted <;> fin_cases first <;> fin_cases second <;>
    simp_all [allowedCompletionShadows] <;> decide

theorem lift_completionShadowNeighborhood_eq_colorNeighborhood
    (twisted : Bool) (q : ThreeColor) (shadow : Fin 16)
    (hcard :
      (k15CompletionShadowNeighborhood twisted q shadow).card = 5) :
    liftK15Finset (k15CompletionShadowNeighborhood twisted q shadow) =
      colorNeighborhood (k16Template twisted) q shadow := by
  let visible := k15CompletionShadowNeighborhood twisted q shadow
  have hsubset : liftK15Finset visible ⊆
      colorNeighborhood (k16Template twisted) q shadow := by
    intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hx
    have hdata := (Finset.mem_filter.mp hx0).2
    exact (mem_colorNeighborhood _ _ _ _).mpr hdata
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [liftK15Finset_card, hcard]
  change colorDegree (k16Template twisted) q shadow ≤ 5
  have hgood : NoMonochromaticTriangle (k16Template twisted) := by
    cases twisted <;>
      simp [k16Template, k16Untwisted_good, k16Twisted_good]
  rw [threeColor_degree_eq_five_at_16 (k16Template twisted) hgood q shadow]

/-- Visible maximum sets in distinct colours are disjoint exactly when
their completion shadows agree. -/
theorem completionShadow_eq_of_disjoint
    (twisted : Bool) (first second : ThreeColor) (hne : first ≠ second)
    (leftShadow rightShadow : Fin 16)
    (hleftCard :
      (k15CompletionShadowNeighborhood twisted first leftShadow).card = 5)
    (hrightCard :
      (k15CompletionShadowNeighborhood twisted second rightShadow).card = 5)
    (hdisjoint : Disjoint
      (k15CompletionShadowNeighborhood twisted first leftShadow)
      (k15CompletionShadowNeighborhood twisted second rightShadow)) :
    leftShadow = rightShadow := by
  have hliftDisjoint : Disjoint
      (liftK15Finset
        (k15CompletionShadowNeighborhood twisted first leftShadow))
      (liftK15Finset
        (k15CompletionShadowNeighborhood twisted second rightShadow)) := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    obtain ⟨xLeft, hxLeftVisible, hxLeftEq⟩ := Finset.mem_image.mp hxLeft
    obtain ⟨xRight, hxRightVisible, hxRightEq⟩ := Finset.mem_image.mp hxRight
    have hxy : xLeft = xRight :=
      (Fin.castSucc_injective 15) (hxLeftEq.trans hxRightEq.symm)
    subst xRight
    exact (Finset.disjoint_left.mp hdisjoint) hxLeftVisible hxRightVisible
  rw [lift_completionShadowNeighborhood_eq_colorNeighborhood
      twisted first leftShadow hleftCard,
    lift_completionShadowNeighborhood_eq_colorNeighborhood
      twisted second rightShadow hrightCard] at hliftDisjoint
  exact (k16Template_differentColorNeighborhood_disjoint_iff
    twisted first second hne leftShadow rightShadow).mp hliftDisjoint

/-! ## Normalized K15 cross matrices -/

abbrev CrossMatrix := Fin 15 → Fin 15 → Option ThreeColor

def rowSet (matrix : CrossMatrix) (source : Fin 15)
    (label : Option ThreeColor) : Finset (Fin 15) :=
  Finset.univ.filter fun target => matrix source target = label

def RowCompatible (targetTwisted : Bool) (matrix : CrossMatrix) : Prop :=
  ∀ source : Fin 15, ∀ q : ThreeColor,
    IsColorIndependentSet (k15Template targetTwisted) q
      (rowSet matrix source (some q))

def commonCount0 (matrix : CrossMatrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor)
    (source : Fin 15) : Nat :=
  (rowSet matrix source (some (palette (otherColor0 wildcard)))).card

def commonCount1 (matrix : CrossMatrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor)
    (source : Fin 15) : Nat :=
  (rowSet matrix source (some (palette (otherColor1 wildcard)))).card

def endpointRowCount (matrix : CrossMatrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor)
    (source : Fin 15) : Nat :=
  (rowSet matrix source none).card +
    (rowSet matrix source (some (palette wildcard))).card

def endpointCount (matrix : CrossMatrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor) : Nat :=
  ∑ source, endpointRowCount matrix palette wildcard source

def doubleSaturatedRows (matrix : CrossMatrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor) :
    Finset (Fin 15) :=
  Finset.univ.filter fun source =>
    commonCount0 matrix palette wildcard source = 5 ∧
      commonCount1 matrix palette wildcard source = 5

/-- Source-side triangle compatibility for the two common colours. -/
def SourceCommonCompatible (sourceTwisted : Bool) (matrix : CrossMatrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor) : Prop :=
  ∀ source1 source2 : Fin 15, source1 ≠ source2 →
    ∀ q : ThreeColor, q ≠ wildcard →
      k15Template sourceTwisted source1 source2 = q →
      Disjoint
        (rowSet matrix source1 (some (palette q)))
        (rowSet matrix source2 (some (palette q)))

theorem row_partition (matrix : CrossMatrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor)
    (source : Fin 15) :
    endpointRowCount matrix palette wildcard source +
      (commonCount0 matrix palette wildcard source +
        commonCount1 matrix palette wildcard source) = 15 := by
  classical
  let fiber : Option ThreeColor → Nat := fun label =>
    (rowSet matrix source label).card
  have hfull : 15 = ∑ label : Option ThreeColor, fiber label := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin 15)))
      (t := (Finset.univ : Finset (Option ThreeColor)))
      (f := matrix source) (by simp)
    simpa [fiber, rowSet] using h
  have hpalette :
      (∑ q : ThreeColor, fiber (some (palette q))) =
        ∑ q : ThreeColor, fiber (some q) :=
    palette.sum_comp (fun q => fiber (some q))
  have hthree :
      fiber (some (palette wildcard)) +
          fiber (some (palette (otherColor0 wildcard))) +
        fiber (some (palette (otherColor1 wildcard))) =
          ∑ q : ThreeColor, fiber (some (palette q)) := by
    fin_cases wildcard <;>
      simp [otherColor0, otherColor1, Fin.sum_univ_succ] <;> omega
  rw [Fintype.sum_option, ← hpalette, ← hthree] at hfull
  simpa [fiber, endpointRowCount, commonCount0, commonCount1,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfull.symm

theorem commonCounts_le_five
    (targetTwisted : Bool) (matrix : CrossMatrix)
    (hcompatible : RowCompatible targetTwisted matrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor) :
    (∀ source, commonCount0 matrix palette wildcard source ≤ 5) ∧
      ∀ source, commonCount1 matrix palette wildcard source ≤ 5 := by
  constructor <;> intro source
  · exact k15Template_independent_card_le_five targetTwisted
      (palette (otherColor0 wildcard)) _
      (hcompatible source (palette (otherColor0 wildcard)))
  · exact k15Template_independent_card_le_five targetTwisted
      (palette (otherColor1 wildcard)) _
      (hcompatible source (palette (otherColor1 wildcard)))

theorem doubleSaturatedRows_card_ge_thirteen_of_endpointCount_le_seventySeven
    (targetTwisted : Bool) (matrix : CrossMatrix)
    (hcompatible : RowCompatible targetTwisted matrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor)
    (hendpoint : endpointCount matrix palette wildcard ≤ 77) :
    13 ≤ (doubleSaturatedRows matrix palette wildcard).card := by
  obtain ⟨h0, h1⟩ := commonCounts_le_five targetTwisted matrix
    hcompatible palette wildcard
  have hpoint (source : Fin 15) :
      commonCount0 matrix palette wildcard source +
          commonCount1 matrix palette wildcard source ≤
        9 + if source ∈ doubleSaturatedRows matrix palette wildcard
          then 1 else 0 := by
    by_cases hsaturated :
        commonCount0 matrix palette wildcard source = 5 ∧
          commonCount1 matrix palette wildcard source = 5
    · simp [doubleSaturatedRows, hsaturated]
    · have hs0 := h0 source
      have hs1 := h1 source
      simp [doubleSaturatedRows, hsaturated]
      omega
  have hcommon :
      (∑ source, (commonCount0 matrix palette wildcard source +
        commonCount1 matrix palette wildcard source)) ≤
      135 + (doubleSaturatedRows matrix palette wildcard).card := by
    calc
      _ ≤ ∑ source : Fin 15,
          (9 + if source ∈ doubleSaturatedRows matrix palette wildcard
            then 1 else 0) :=
        Finset.sum_le_sum fun source _ => hpoint source
      _ = 135 + (doubleSaturatedRows matrix palette wildcard).card := by
        simp [Finset.sum_add_distrib]
  have htotal :
      endpointCount matrix palette wildcard +
        ∑ source, (commonCount0 matrix palette wildcard source +
          commonCount1 matrix palette wildcard source) = 225 := by
    rw [endpointCount, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _source : Fin 15, 15 :=
        Finset.sum_congr rfl fun source _ =>
          row_partition matrix palette wildcard source
      _ = 225 := by simp
  omega

/-! ## The six-shadow obstruction -/

theorem doubleSaturatedRows_card_le_twelve
    (sourceTwisted targetTwisted : Bool) (matrix : CrossMatrix)
    (hrow : RowCompatible targetTwisted matrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor)
    (hsource : SourceCommonCompatible sourceTwisted matrix palette wildcard) :
    (doubleSaturatedRows matrix palette wildcard).card ≤ 12 := by
  classical
  let domain := doubleSaturatedRows matrix palette wildcard
  let first := palette (otherColor0 wildcard)
  let second := palette (otherColor1 wildcard)
  have hfirstSecond : first ≠ second :=
    palette.injective.ne (otherColor0_ne_otherColor1 wildcard)
  have hshadowExists (source : Fin 15) (hsourceDomain : source ∈ domain) :
      ∃! shadow : Fin 16,
        rowSet matrix source (some first) =
            k15CompletionShadowNeighborhood targetTwisted first shadow ∧
          rowSet matrix source (some second) =
            k15CompletionShadowNeighborhood targetTwisted second shadow := by
    have hsaturated := (Finset.mem_filter.mp hsourceDomain).2
    have hfirstCard : (rowSet matrix source (some first)).card = 5 := by
      simpa [domain, first, commonCount0] using hsaturated.1
    have hsecondCard : (rowSet matrix source (some second)).card = 5 := by
      simpa [domain, second, commonCount1] using hsaturated.2
    obtain ⟨firstShadow, hfirstShadow, hfirstUnique⟩ :=
      k15Template_maxIndependentSet_unique_completionShadow
        targetTwisted first (rowSet matrix source (some first))
        hfirstCard (hrow source first)
    obtain ⟨secondShadow, hsecondShadow, _⟩ :=
      k15Template_maxIndependentSet_unique_completionShadow
        targetTwisted second (rowSet matrix source (some second))
        hsecondCard (hrow source second)
    have hsetsDisjoint : Disjoint
        (rowSet matrix source (some first))
        (rowSet matrix source (some second)) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxFirst hxSecond
      have hfirstLabel := (Finset.mem_filter.mp hxFirst).2
      have hsecondLabel := (Finset.mem_filter.mp hxSecond).2
      exact hfirstSecond (Option.some.inj (hfirstLabel.symm.trans hsecondLabel))
    have hshadows : firstShadow = secondShadow :=
      completionShadow_eq_of_disjoint targetTwisted first second hfirstSecond
        firstShadow secondShadow
        (by simpa [← hfirstShadow] using hfirstCard)
        (by simpa [← hsecondShadow] using hsecondCard)
        (by simpa [← hfirstShadow, ← hsecondShadow] using hsetsDisjoint)
    subst secondShadow
    refine ⟨firstShadow, ⟨hfirstShadow, hsecondShadow⟩, ?_⟩
    intro other hother
    exact hfirstUnique other hother.1
  let shadow : Fin 15 → Fin 16 := fun source =>
    if hsourceDomain : source ∈ domain then
      Classical.choose (hshadowExists source hsourceDomain)
    else 0
  have hshadow (source : Fin 15) (hsourceDomain : source ∈ domain) :
      rowSet matrix source (some first) =
          k15CompletionShadowNeighborhood targetTwisted first (shadow source) ∧
        rowSet matrix source (some second) =
          k15CompletionShadowNeighborhood targetTwisted second (shadow source) := by
    simp only [shadow, dif_pos hsourceDomain]
    exact (Classical.choose_spec (hshadowExists source hsourceDomain)).1
  have hmapsTo (source : Fin 15) (hsourceDomain : source ∈ domain) :
      shadow source ∈ allowedCompletionShadows targetTwisted first second := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hfive := (Finset.mem_filter.mp hsourceDomain).2.1
      have hfive' : (rowSet matrix source (some first)).card = 5 := by
        simpa [first, commonCount0] using hfive
      simpa [← (hshadow source hsourceDomain).1] using hfive'
    · have hfive := (Finset.mem_filter.mp hsourceDomain).2.2
      have hfive' : (rowSet matrix source (some second)).card = 5 := by
        simpa [second, commonCount1] using hfive
      simpa [← (hshadow source hsourceDomain).2] using hfive'
  by_contra hcard
  have hcard13 : 12 < domain.card := by simpa [domain] using (Nat.lt_of_not_ge hcard)
  have hallowedCard :
      (allowedCompletionShadows targetTwisted first second).card = 6 :=
    allowedCompletionShadows_card targetTwisted first second hfirstSecond
  have hlargeFiber : ∃ commonShadow ∈
      allowedCompletionShadows targetTwisted first second,
      2 < (domain.filter fun source => shadow source = commonShadow).card := by
    by_contra hnone
    push Not at hnone
    have hfiberBound (commonShadow : Fin 16)
        (hcommonShadow : commonShadow ∈
          allowedCompletionShadows targetTwisted first second) :
        (domain.filter fun source => shadow source = commonShadow).card ≤ 2 :=
      hnone commonShadow hcommonShadow
    have hsum := Finset.card_eq_sum_card_fiberwise hmapsTo
    have hsumBound :
        (∑ commonShadow ∈
          allowedCompletionShadows targetTwisted first second,
          (domain.filter fun source => shadow source = commonShadow).card) ≤
        ∑ _commonShadow ∈
          allowedCompletionShadows targetTwisted first second, 2 := by
      exact Finset.sum_le_sum fun commonShadow hcommonShadow =>
        hfiberBound commonShadow hcommonShadow
    rw [← hsum] at hsumBound
    have hrhs :
        (∑ _commonShadow ∈
          allowedCompletionShadows targetTwisted first second, 2) = 12 := by
      simp [hallowedCard]
    rw [hrhs] at hsumBound
    omega
  obtain ⟨commonShadow, _hcommonAllowed, hfiber⟩ := hlargeFiber
  let fiber := domain.filter fun source => shadow source = commonShadow
  have hfiber3 : 2 < fiber.card := by simpa [fiber] using hfiber
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hfiber3
  have hpairWildcard (left right : Fin 15)
      (hleft : left ∈ fiber) (hright : right ∈ fiber)
      (hne : left ≠ right) :
      k15Template sourceTwisted left right = wildcard := by
    by_contra hnotWildcard
    obtain hq0 | hq1 := eq_otherColor_of_ne wildcard
      (k15Template sourceTwisted left right) hnotWildcard
    · have hdisjoint := hsource left right hne (otherColor0 wildcard)
        (otherColor0_ne wildcard) hq0
      have hleftDomain := (Finset.mem_filter.mp hleft).1
      have hrightDomain := (Finset.mem_filter.mp hright).1
      have hleftShadow := (Finset.mem_filter.mp hleft).2
      have hrightShadow := (Finset.mem_filter.mp hright).2
      change Disjoint (rowSet matrix left (some first))
        (rowSet matrix right (some first)) at hdisjoint
      rw [(hshadow left hleftDomain).1,
        (hshadow right hrightDomain).1,
        hleftShadow, hrightShadow] at hdisjoint
      have hnonempty :
          (k15CompletionShadowNeighborhood targetTwisted first commonShadow).Nonempty :=
        Finset.card_pos.mp (by
          have hfive := (Finset.mem_filter.mp hleftDomain).2.1
          have hfive' : (rowSet matrix left (some first)).card = 5 := by
            simpa [first, commonCount0] using hfive
          rw [(hshadow left hleftDomain).1, hleftShadow] at hfive'
          omega)
      obtain ⟨a, ha⟩ := hnonempty
      exact (Finset.disjoint_left.mp hdisjoint) ha ha
    · have hdisjoint := hsource left right hne (otherColor1 wildcard)
        (otherColor1_ne wildcard) hq1
      have hleftDomain := (Finset.mem_filter.mp hleft).1
      have hrightDomain := (Finset.mem_filter.mp hright).1
      have hleftShadow := (Finset.mem_filter.mp hleft).2
      have hrightShadow := (Finset.mem_filter.mp hright).2
      change Disjoint (rowSet matrix left (some second))
        (rowSet matrix right (some second)) at hdisjoint
      rw [(hshadow left hleftDomain).2,
        (hshadow right hrightDomain).2,
        hleftShadow, hrightShadow] at hdisjoint
      have hnonempty :
          (k15CompletionShadowNeighborhood targetTwisted second commonShadow).Nonempty :=
        Finset.card_pos.mp (by
          have hfive := (Finset.mem_filter.mp hleftDomain).2.2
          have hfive' : (rowSet matrix left (some second)).card = 5 := by
            simpa [second, commonCount1] using hfive
          rw [(hshadow left hleftDomain).2, hleftShadow] at hfive'
          omega)
      obtain ⟨a, ha⟩ := hnonempty
      exact (Finset.disjoint_left.mp hdisjoint) ha ha
  have htriangle : HomogeneousTriangle
      (k15Template sourceTwisted) x y z := by
    constructor
    · rw [hpairWildcard x y hx hy hxy,
        hpairWildcard x z hx hz hxz]
    · rw [hpairWildcard x z hx hz hxz,
        hpairWildcard y z hy hz hyz]
  have hgood : NoMonochromaticTriangle (k15Template sourceTwisted) := by
    cases sourceTwisted <;>
      simp [k15Template, k15Untwisted_good, k15Twisted_good]
  exact hgood x y z ⟨hxy, hxz, hyz⟩ htriangle

/-- Main local cut: the two endpoint colours occupy at least 78 positions
in every triangle-compatible cross matrix between critical K15 blocks. -/
theorem endpointCount_ge_seventyEight
    (sourceTwisted targetTwisted : Bool) (matrix : CrossMatrix)
    (hrow : RowCompatible targetTwisted matrix)
    (palette : ThreeColor ≃ ThreeColor) (wildcard : ThreeColor)
    (hsource : SourceCommonCompatible sourceTwisted matrix palette wildcard) :
    78 ≤ endpointCount matrix palette wildcard := by
  by_contra hbound
  have hle : endpointCount matrix palette wildcard ≤ 77 := by omega
  have hlower :=
    doubleSaturatedRows_card_ge_thirteen_of_endpointCount_le_seventySeven
      targetTwisted matrix hrow palette wildcard hle
  have hupper := doubleSaturatedRows_card_le_twelve
    sourceTwisted targetTwisted matrix hrow palette wildcard hsource
  omega

#print axioms R4333.K15PairEndpointBound.endpointCount_ge_seventyEight

end K15PairEndpointBound
end R4333
