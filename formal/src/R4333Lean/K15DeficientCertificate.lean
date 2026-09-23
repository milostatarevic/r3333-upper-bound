import R4333Lean.CatalogueBaseCNFLeavesK15Refined
import R4333Lean.K15Extension
import R4333Lean.ColorRelabel
import Mathlib.Data.Fintype.EquivFin

/-!
# Certified deficient-edge rule for critical three-colourings on fifteen vertices

This file supplies the mathematical normalization missing between an arbitrary
bad deficient edge and the small, kernel-checked LRAT leaves.  No graph
catalogue or externally computed isomorphism is used: vertices are relabelled
by an equivalence between the fibres of their two endpoint colours.
-/

namespace R4333

open FiniteColorCNF CatalogueBaseCNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The finite key used to build the normalizing vertex equivalence. -/
inductive K15EndpointKey where
  | first
  | second
  | pair (fromFirst fromSecond : ThreeColor)
  deriving DecidableEq

/-- A half-open interval of canonical labels. -/
def fin15Interval (lo hi : Nat) : Finset (Fin 15) :=
  Finset.univ.filter fun i => lo ≤ i.val ∧ i.val < hi

@[simp] theorem mem_fin15Interval (lo hi : Nat) (i : Fin 15) :
    i ∈ fin15Interval lo hi ↔ lo ≤ i.val ∧ i.val < hi := by
  simp [fin15Interval]

theorem card_fin15Interval (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ 15) :
    (fin15Interval lo hi).card = hi - lo := by
  let e : {i // i ∈ fin15Interval lo hi} ≃ Fin (hi - lo) :=
    { toFun := fun i => ⟨i.1.val - lo, by
        have hi_mem := (mem_fin15Interval lo hi i).mp i.2
        omega⟩
      invFun := fun j => ⟨⟨lo + j.val, by omega⟩, by
        apply (mem_fin15Interval lo hi _).mpr
        change lo ≤ lo + j.val ∧ lo + j.val < hi
        omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        change lo + (i.1.val - lo) = i.1.val
        have hi_mem := (mem_fin15Interval lo hi i).mp i.2
        omega
      right_inv := by
        intro j
        apply Fin.ext
        change (lo + j.val) - lo = j.val
        omega }
  rw [← Fintype.card_coe]
  simpa using Fintype.card_congr e

/-- The vertices other than the two selected endpoints. -/
def awayFrom (u v : Fin 15) : Finset (Fin 15) :=
  (Finset.univ.erase u).erase v

/-- A two-endpoint colour cell. -/
def endpointCell (d : EdgeColoring (Fin 15) ThreeColor)
    (u v : Fin 15) (p q : ThreeColor) : Finset (Fin 15) :=
  (awayFrom u v).filter fun x => d u x = p ∧ d v x = q

/-- A row of the endpoint-colour matrix. -/
def endpointRow (d : EdgeColoring (Fin 15) ThreeColor)
    (u v : Fin 15) (p : ThreeColor) : Finset (Fin 15) :=
  (awayFrom u v).filter fun x => d u x = p

/-- A column of the endpoint-colour matrix. -/
def endpointColumn (d : EdgeColoring (Fin 15) ThreeColor)
    (u v : Fin 15) (q : ThreeColor) : Finset (Fin 15) :=
  (awayFrom u v).filter fun x => d v x = q

theorem endpointRow_eq_erase_neighborhood
    (d : EdgeColoring (Fin 15) ThreeColor) (u v : Fin 15)
    (p : ThreeColor) :
    endpointRow d u v p = (colorNeighborhood d p u).erase v := by
  ext x
  simp [endpointRow, awayFrom, colorNeighborhood, and_assoc, and_left_comm,
    and_comm]

theorem endpointColumn_eq_erase_neighborhood
    (d : EdgeColoring (Fin 15) ThreeColor) (u v : Fin 15)
    (q : ThreeColor) :
    endpointColumn d u v q = (colorNeighborhood d q v).erase u := by
  ext x
  simp [endpointColumn, awayFrom, colorNeighborhood, and_assoc,
    and_comm]

theorem endpointRow_card_eq_sum_cells
    (d : EdgeColoring (Fin 15) ThreeColor) (u v : Fin 15)
    (p : ThreeColor) :
    (endpointRow d u v p).card =
      (endpointCell d u v p 0).card +
      ((endpointCell d u v p 1).card + (endpointCell d u v p 2).card) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := endpointRow d u v p) (t := Finset.univ)
    (f := fun x => d v x) (by simp)
  simpa [Fin.sum_univ_succ, endpointRow, endpointCell, Finset.filter_filter, and_assoc,
    and_left_comm, and_comm] using h

theorem endpointColumn_card_eq_sum_cells
    (d : EdgeColoring (Fin 15) ThreeColor) (u v : Fin 15)
    (q : ThreeColor) :
    (endpointColumn d u v q).card =
      (endpointCell d u v 0 q).card +
      ((endpointCell d u v 1 q).card + (endpointCell d u v 2 q).card) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := endpointColumn d u v q) (t := Finset.univ)
    (f := fun x => d u x) (by simp)
  simpa [Fin.sum_univ_succ, endpointColumn, endpointCell, Finset.filter_filter, and_assoc,
    and_left_comm, and_comm] using h

/-- The endpoint-colour matrix of a putative bad deficient edge has fixed row
and column sums.  The `(0,0)` cell is empty by triangle-freeness. -/
theorem k15_bad_endpoint_matrix
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    (endpointCell d u v 0 0).card = 0 ∧
    (endpointCell d u v 0 0).card +
      ((endpointCell d u v 0 1).card + (endpointCell d u v 0 2).card) = 3 ∧
    (endpointCell d u v 1 0).card +
      ((endpointCell d u v 1 1).card + (endpointCell d u v 1 2).card) = 5 ∧
    (endpointCell d u v 2 0).card +
      ((endpointCell d u v 2 1).card + (endpointCell d u v 2 2).card) = 5 ∧
    (endpointCell d u v 0 0).card +
      ((endpointCell d u v 1 0).card + (endpointCell d u v 2 0).card) = 3 ∧
    (endpointCell d u v 0 1).card +
      ((endpointCell d u v 1 1).card + (endpointCell d u v 2 1).card) = 5 ∧
    (endpointCell d u v 0 2).card +
      ((endpointCell d u v 1 2).card + (endpointCell d u v 2 2).card) = 5 := by
  classical
  have hsumu := sum_colorDegree_eq_card_sub_one d u
  have hsumv := sum_colorDegree_eq_card_sub_one d v
  have hdu1 := threeColor_degree_four_or_five_at_15 d hd (1 : ThreeColor) u
  have hdu2 := threeColor_degree_four_or_five_at_15 d hd (2 : ThreeColor) u
  have hdv1 := threeColor_degree_four_or_five_at_15 d hd (1 : ThreeColor) v
  have hdv2 := threeColor_degree_four_or_five_at_15 d hd (2 : ThreeColor) v
  have hdu1' : colorDegree d 1 u = 5 := by
    simp [Fin.sum_univ_succ] at hsumu
    omega
  have hdu2' : colorDegree d 2 u = 5 := by
    simp [Fin.sum_univ_succ] at hsumu
    omega
  have hdv1' : colorDegree d 1 v = 5 := by
    simp [Fin.sum_univ_succ] at hsumv
    omega
  have hdv2' : colorDegree d 2 v = 5 := by
    simp [Fin.sum_univ_succ] at hsumv
    omega
  have hrow0 : (endpointRow d u v 0).card = 3 := by
    rw [endpointRow_eq_erase_neighborhood]
    have hmem : v ∈ colorNeighborhood d 0 u := by simp [huv.symm, hedge]
    have := Finset.card_erase_add_one hmem
    change (colorNeighborhood d 0 u).card = 4 at hdu
    omega
  have hrow1 : (endpointRow d u v 1).card = 5 := by
    rw [endpointRow_eq_erase_neighborhood]
    have hnot : v ∉ colorNeighborhood d 1 u := by
      simp only [mem_colorNeighborhood, not_and_or]
      exact Or.inr (by simp [hedge])
    rw [Finset.erase_eq_of_notMem hnot]
    exact hdu1'
  have hrow2 : (endpointRow d u v 2).card = 5 := by
    rw [endpointRow_eq_erase_neighborhood]
    have hnot : v ∉ colorNeighborhood d 2 u := by
      simp only [mem_colorNeighborhood, not_and_or]
      exact Or.inr (by simp [hedge])
    rw [Finset.erase_eq_of_notMem hnot]
    exact hdu2'
  have hcol0 : (endpointColumn d u v 0).card = 3 := by
    rw [endpointColumn_eq_erase_neighborhood]
    have hmem : u ∈ colorNeighborhood d 0 v := by
      simp [huv, d.color_symm, hedge]
    have := Finset.card_erase_add_one hmem
    change (colorNeighborhood d 0 v).card = 4 at hdv
    omega
  have hcol1 : (endpointColumn d u v 1).card = 5 := by
    rw [endpointColumn_eq_erase_neighborhood]
    have hnot : u ∉ colorNeighborhood d 1 v := by
      simp only [mem_colorNeighborhood, not_and_or]
      exact Or.inr (by simp [d.color_symm, hedge])
    rw [Finset.erase_eq_of_notMem hnot]
    exact hdv1'
  have hcol2 : (endpointColumn d u v 2).card = 5 := by
    rw [endpointColumn_eq_erase_neighborhood]
    have hnot : u ∉ colorNeighborhood d 2 v := by
      simp only [mem_colorNeighborhood, not_and_or]
      exact Or.inr (by simp [d.color_symm, hedge])
    rw [Finset.erase_eq_of_notMem hnot]
    exact hdv2'
  have h00 : endpointCell d u v 0 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [endpointCell, Finset.mem_filter] at hx
    rcases hx with ⟨haway, hux, hvx⟩
    have haway' : x ≠ v ∧ x ≠ u := by simpa [awayFrom] using haway
    have hxu : x ≠ u := haway'.2
    have hxv : x ≠ v := haway'.1
    exact hd u v x ⟨huv, hxu.symm, hxv.symm⟩
      ⟨hedge.trans hux.symm, hux.trans hvx.symm⟩
  rw [endpointRow_card_eq_sum_cells] at hrow0 hrow1 hrow2
  rw [endpointColumn_card_eq_sum_cells] at hcol0 hcol1 hcol2
  exact ⟨by simp [h00], hrow0, hrow1, hrow2, hcol0, hcol1, hcol2⟩

/-- Key of an original vertex relative to the selected endpoints. -/
def actualEndpointKey (d : EdgeColoring (Fin 15) ThreeColor)
    (u v x : Fin 15) : K15EndpointKey :=
  if x = u then .first else if x = v then .second else .pair (d u x) (d v x)

/-- Canonical label key.  The parameters are the `(0,1)`, `(1,0)`, and
`(1,1)` cell sizes respectively. -/
def canonicalEndpointKey (redFirst blueRed blueBlue : Nat)
    (x : Fin 15) : K15EndpointKey :=
  if x.val = 0 then .first
  else if x.val = 1 then .second
  else if x.val < 5 then
    .pair 0 (if x.val < 2 + redFirst then 1 else 2)
  else if x.val < 10 then
    .pair 1 (if x.val < 5 + blueRed then 0
      else if x.val < 5 + blueRed + blueBlue then 1 else 2)
  else
    .pair 2 (if x.val < 13 - blueRed then 0
      else if x.val < 18 - blueRed - redFirst - blueBlue then 1 else 2)

def canonicalFirstColor (x : Fin 15) : ThreeColor :=
  if x.val < 5 then 0 else if x.val < 10 then 1 else 2

def canonicalSecondColor (redFirst blueRed blueBlue : Nat)
    (x : Fin 15) : ThreeColor :=
  if x.val < 5 then (if x.val < 2 + redFirst then 1 else 2)
  else if x.val < 10 then
    (if x.val < 5 + blueRed then 0
      else if x.val < 5 + blueRed + blueBlue then 1 else 2)
  else
    (if x.val < 13 - blueRed then 0
      else if x.val < 18 - blueRed - redFirst - blueBlue then 1 else 2)

theorem canonicalEndpointKey_of_ne_roots
    (redFirst blueRed blueBlue : Nat) (x : Fin 15)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    canonicalEndpointKey redFirst blueRed blueBlue x =
      .pair (canonicalFirstColor x)
        (canonicalSecondColor redFirst blueRed blueBlue x) := by
  have hx0' : x.val ≠ 0 := by
    intro h
    apply hx0
    apply Fin.ext
    exact h
  have hx1' : x.val ≠ 1 := by
    intro h
    apply hx1
    apply Fin.ext
    exact h
  simp [canonicalEndpointKey, canonicalFirstColor, canonicalSecondColor, hx0', hx1']
  split_ifs <;> rfl

theorem actualEndpointKey_eq_pair_iff
    (d : EdgeColoring (Fin 15) ThreeColor) (u v x : Fin 15)
    (p q : ThreeColor) :
    actualEndpointKey d u v x = .pair p q ↔
      x ≠ u ∧ x ≠ v ∧ d u x = p ∧ d v x = q := by
  unfold actualEndpointKey
  by_cases hxu : x = u
  · simp [hxu]
  · by_cases hxv : x = v
    · subst x
      simp [hxu]
    · simp [hxu, hxv]

/-- The nine canonical intervals, in the exact order used by the refined
LRAT leaves. -/
def canonicalEndpointCell (redFirst blueRed blueBlue : Nat)
    (p q : ThreeColor) : Finset (Fin 15) :=
  if p = 0 ∧ q = 0 then ∅
  else if p = 0 ∧ q = 1 then fin15Interval 2 (2 + redFirst)
  else if p = 0 ∧ q = 2 then fin15Interval (2 + redFirst) 5
  else if p = 1 ∧ q = 0 then fin15Interval 5 (5 + blueRed)
  else if p = 1 ∧ q = 1 then
    fin15Interval (5 + blueRed) (5 + blueRed + blueBlue)
  else if p = 1 ∧ q = 2 then
    fin15Interval (5 + blueRed + blueBlue) 10
  else if p = 2 ∧ q = 0 then fin15Interval 10 (13 - blueRed)
  else if p = 2 ∧ q = 1 then
    fin15Interval (13 - blueRed) (18 - blueRed - redFirst - blueBlue)
  else fin15Interval (18 - blueRed - redFirst - blueBlue) 15

theorem actualEndpointKey_pair_fiber
    (d : EdgeColoring (Fin 15) ThreeColor) (u v : Fin 15) (huv : u ≠ v)
    (p q : ThreeColor) :
    Finset.univ.filter (fun x => actualEndpointKey d u v x = .pair p q) =
      endpointCell d u v p q := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, endpointCell,
    actualEndpointKey, awayFrom, Finset.mem_erase]
  by_cases hxu : x = u
  · subst x
    simp [huv]
  · by_cases hxv : x = v
    · subst x
      simp [hxu]
    · simp [hxu, hxv]

theorem actualEndpointKey_first_fiber
    (d : EdgeColoring (Fin 15) ThreeColor) (u v : Fin 15) (_huv : u ≠ v) :
    Finset.univ.filter (fun x => actualEndpointKey d u v x = .first) = {u} := by
  ext x
  by_cases hxu : x = u
  · simp [hxu, actualEndpointKey]
  · by_cases hxv : x = v
    · subst x
      simp [hxu, actualEndpointKey]
    · simp [hxu, hxv, actualEndpointKey]

theorem actualEndpointKey_second_fiber
    (d : EdgeColoring (Fin 15) ThreeColor) (u v : Fin 15) (huv : u ≠ v) :
    Finset.univ.filter (fun x => actualEndpointKey d u v x = .second) = {v} := by
  ext x
  by_cases hxu : x = u
  · subst x
    simp [actualEndpointKey, huv]
  · by_cases hxv : x = v
    · simp [hxv, actualEndpointKey, huv.symm]
    · simp [hxu, hxv, actualEndpointKey]

theorem canonicalEndpointKey_first_fiber (redFirst blueRed blueBlue : Nat) :
    Finset.univ.filter
      (fun x => canonicalEndpointKey redFirst blueRed blueBlue x = .first) = {0} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  simp [canonicalEndpointKey]
  split_ifs
  all_goals simp_all

theorem canonicalEndpointKey_second_fiber (redFirst blueRed blueBlue : Nat) :
    Finset.univ.filter
      (fun x => canonicalEndpointKey redFirst blueRed blueBlue x = .second) = {1} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    simp only [canonicalEndpointKey] at h
    split_ifs at h
    all_goals simp at h
    exact Fin.ext (by assumption)
  · intro hx
    subst x
    simp [canonicalEndpointKey]

theorem canonicalEndpointKey_pair_fiber
    (redFirst blueRed blueBlue : Nat)
    (ha : redFirst ≤ 3) (hr : blueRed ≤ 3)
    (hrb : blueRed + blueBlue ≤ 5)
    (hab : redFirst + blueBlue ≤ 5)
    (hlow : 3 ≤ blueRed + redFirst + blueBlue)
    (p q : ThreeColor) :
    Finset.univ.filter
      (fun x => canonicalEndpointKey redFirst blueRed blueBlue x = .pair p q) =
      canonicalEndpointCell redFirst blueRed blueBlue p q := by
  ext x
  fin_cases p <;> fin_cases q <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  all_goals
    simp [canonicalEndpointKey, canonicalEndpointCell, fin15Interval]
    split_ifs <;> simp at * <;> omega

/-- The three parameters extracted from a bad endpoint matrix satisfy the
bounds used by the normalized cubes, and its nine actual cells have the same
sizes as the nine canonical intervals. -/
theorem k15_endpoint_parameter_facts
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    let redFirst := (endpointCell d u v 0 1).card
    let blueRed := (endpointCell d u v 1 0).card
    let blueBlue := (endpointCell d u v 1 1).card
    redFirst ≤ 3 ∧ blueRed ≤ 3 ∧ blueRed + blueBlue ≤ 5 ∧
      redFirst + blueBlue ≤ 5 ∧
      3 ≤ blueRed + redFirst + blueBlue ∧
      ∀ p q : ThreeColor,
        (canonicalEndpointCell redFirst blueRed blueBlue p q).card =
          (endpointCell d u v p q).card := by
  dsimp only
  rcases k15_bad_endpoint_matrix d hd u v huv hedge hdu hdv with
    ⟨h00, hrow0, hrow1, hrow2, hcol0, hcol1, hcol2⟩
  have ha : (endpointCell d u v 0 1).card ≤ 3 := by omega
  have hr : (endpointCell d u v 1 0).card ≤ 3 := by omega
  have hrb : (endpointCell d u v 1 0).card +
      (endpointCell d u v 1 1).card ≤ 5 := by omega
  have hab : (endpointCell d u v 0 1).card +
      (endpointCell d u v 1 1).card ≤ 5 := by omega
  have hlow : 3 ≤ (endpointCell d u v 1 0).card +
      (endpointCell d u v 0 1).card +
      (endpointCell d u v 1 1).card := by omega
  refine ⟨ha, hr, hrb, hab, hlow, ?_⟩
  intro p q
  fin_cases p <;> fin_cases q
  all_goals simp [canonicalEndpointCell, h00]
  all_goals rw [card_fin15Interval] <;> omega

theorem k15_endpoint_key_fiber_card_eq
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    let redFirst := (endpointCell d u v 0 1).card
    let blueRed := (endpointCell d u v 1 0).card
    let blueBlue := (endpointCell d u v 1 1).card
    ∀ key : K15EndpointKey,
      Fintype.card {x : Fin 15 //
        canonicalEndpointKey redFirst blueRed blueBlue x = key} =
      Fintype.card {x : Fin 15 // actualEndpointKey d u v x = key} := by
  dsimp only
  rcases k15_endpoint_parameter_facts d hd u v huv hedge hdu hdv with
    ⟨ha, hr, hrb, hab, hlow, hcells⟩
  intro key
  rw [Fintype.card_subtype, Fintype.card_subtype]
  cases key with
  | first =>
      rw [canonicalEndpointKey_first_fiber, actualEndpointKey_first_fiber d u v huv]
      simp
  | second =>
      rw [canonicalEndpointKey_second_fiber, actualEndpointKey_second_fiber d u v huv]
      simp
  | pair p q =>
      rw [canonicalEndpointKey_pair_fiber _ _ _ ha hr hrb hab hlow,
        actualEndpointKey_pair_fiber d u v huv, hcells p q]

/-- The canonical-label-to-original-vertex equivalence obtained by matching
the endpoint-key fibres. -/
noncomputable def k15EndpointEquiv
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    Fin 15 ≃ Fin 15 := by
  let redFirst := (endpointCell d u v 0 1).card
  let blueRed := (endpointCell d u v 1 0).card
  let blueBlue := (endpointCell d u v 1 1).card
  exact Equiv.ofFiberEquiv fun key =>
    Fintype.equivOfCardEq
      (k15_endpoint_key_fiber_card_eq d hd u v huv hedge hdu hdv key)

theorem k15EndpointEquiv_key
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4)
    (x : Fin 15) :
    actualEndpointKey d u v (k15EndpointEquiv d hd u v huv hedge hdu hdv x) =
      canonicalEndpointKey (endpointCell d u v 0 1).card
        (endpointCell d u v 1 0).card (endpointCell d u v 1 1).card x := by
  exact Equiv.ofFiberEquiv_map (fun key => Fintype.equivOfCardEq
    (k15_endpoint_key_fiber_card_eq d hd u v huv hedge hdu hdv key)) x

theorem k15EndpointEquiv_zero
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    k15EndpointEquiv d hd u v huv hedge hdu hdv 0 = u := by
  have hk := k15EndpointEquiv_key d hd u v huv hedge hdu hdv (0 : Fin 15)
  have hk' : actualEndpointKey d u v
      (k15EndpointEquiv d hd u v huv hedge hdu hdv 0) = .first := by
    simpa [canonicalEndpointKey] using hk
  have hm : k15EndpointEquiv d hd u v huv hedge hdu hdv 0 ∈
      Finset.univ.filter (fun x => actualEndpointKey d u v x = .first) := by
    simp [hk']
  rw [actualEndpointKey_first_fiber d u v huv] at hm
  simpa using hm

theorem k15EndpointEquiv_one
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    k15EndpointEquiv d hd u v huv hedge hdu hdv 1 = v := by
  have hk := k15EndpointEquiv_key d hd u v huv hedge hdu hdv (1 : Fin 15)
  have hk' : actualEndpointKey d u v
      (k15EndpointEquiv d hd u v huv hedge hdu hdv 1) = .second := by
    simpa [canonicalEndpointKey] using hk
  have hm : k15EndpointEquiv d hd u v huv hedge hdu hdv 1 ∈
      Finset.univ.filter (fun x => actualEndpointKey d u v x = .second) := by
    simp [hk']
  rw [actualEndpointKey_second_fiber d u v huv] at hm
  simpa using hm

/-- The fully normalized labelled colouring attached to a bad endpoint edge. -/
noncomputable def normalizedBadK15
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    EdgeColoring (Fin 15) ThreeColor :=
  relabelVertices d (k15EndpointEquiv d hd u v huv hedge hdu hdv)

theorem normalizedBadK15_good
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    NoMonochromaticTriangle (normalizedBadK15 d hd u v huv hedge hdu hdv) :=
  noMono_relabelVertices d _ hd

theorem normalizedBadK15_edge_zero_one
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    normalizedBadK15 d hd u v huv hedge hdu hdv 0 1 = 0 := by
  simp [normalizedBadK15, k15EndpointEquiv_zero d hd u v huv hedge hdu hdv,
    k15EndpointEquiv_one d hd u v huv hedge hdu hdv, hedge]

theorem normalizedBadK15_root_colors
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4)
    (x : Fin 15) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    normalizedBadK15 d hd u v huv hedge hdu hdv 0 x = canonicalFirstColor x ∧
    normalizedBadK15 d hd u v huv hedge hdu hdv 1 x =
      canonicalSecondColor (endpointCell d u v 0 1).card
        (endpointCell d u v 1 0).card (endpointCell d u v 1 1).card x := by
  have hk := k15EndpointEquiv_key d hd u v huv hedge hdu hdv x
  rw [canonicalEndpointKey_of_ne_roots _ _ _ x hx0 hx1] at hk
  have hp := (actualEndpointKey_eq_pair_iff d u v _ _ _).mp hk
  constructor
  · simpa [normalizedBadK15,
      k15EndpointEquiv_zero d hd u v huv hedge hdu hdv] using hp.2.2.1
  · simpa [normalizedBadK15,
      k15EndpointEquiv_one d hd u v huv hedge hdu hdv] using hp.2.2.2

namespace K15LeafSemantics

theorem satisfies_fmla_append (valuation : Sat.Valuation) (a b : Sat.Fmla)
    (ha : valuation.satisfies_fmla a) (hb : valuation.satisfies_fmla b) :
    valuation.satisfies_fmla (a ++ b) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with h | h
  · exact ha.prop clause h
  · exact hb.prop clause h

theorem satisfies_positive_unit (valuation : Sat.Valuation) (atom : Nat)
    (h : valuation atom) : valuation.satisfies [Sat.Literal.pos atom] := by
  change (¬valuation atom) → False
  exact fun hn => hn h

theorem satisfies_negative_unit (valuation : Sat.Valuation) (atom : Nat)
    (h : ¬valuation atom) : valuation.satisfies [Sat.Literal.neg atom] := by
  change valuation atom → False
  exact fun hp => h hp

theorem coloringValuation_satisfies_setEdge
    (c : EdgeColoring (Fin 15) ThreeColor)
    (a b q : Nat) (ha : a < 15) (hb : b < 15) (hq : q < 3)
    (hcolor : c ⟨a, ha⟩ ⟨b, hb⟩ = ⟨q, hq⟩) :
    (coloringValuation c).satisfies_fmla (setEdge a b q) := by
  constructor
  intro clause hclause
  simp only [setEdge, List.mem_cons, List.not_mem_nil, or_false] at hclause
  subst clause
  apply satisfies_positive_unit
  exact (coloringValuation_edgeAtom c ⟨a, ha⟩ ⟨b, hb⟩ ⟨q, hq⟩).2 hcolor

theorem coloringValuation_satisfies_forbidEdge
    (c : EdgeColoring (Fin 15) ThreeColor)
    (a b q : Nat) (ha : a < 15) (hb : b < 15) (hq : q < 3)
    (hcolor : c ⟨a, ha⟩ ⟨b, hb⟩ ≠ ⟨q, hq⟩) :
    (coloringValuation c).satisfies_fmla (forbidEdge a b q) := by
  constructor
  intro clause hclause
  simp only [forbidEdge, List.mem_cons, List.not_mem_nil, or_false] at hclause
  subst clause
  apply satisfies_negative_unit
  intro hv
  apply hcolor
  exact (coloringValuation_edgeAtom c ⟨a, ha⟩ ⟨b, hb⟩ ⟨q, hq⟩).1 hv

theorem coloringValuation_satisfies_setRootBlock
    (c : EdgeColoring (Fin 15) ThreeColor)
    (root start length color : Nat)
    (hroot : root < 15) (hbound : start + length ≤ 15) (hcolorBound : color < 3)
    (hcolors : ∀ position (hpos : position < length),
      c ⟨root, hroot⟩ ⟨start + position, by omega⟩ = ⟨color, hcolorBound⟩) :
    (coloringValuation c).satisfies_fmla
      (setRootBlock root start length color) := by
  constructor
  intro clause hclause
  simp only [setRootBlock, List.mem_map] at hclause
  obtain ⟨vertex, hvertex, rfl⟩ := hclause
  simp only [interval, List.mem_map] at hvertex
  obtain ⟨position, hposition, rfl⟩ := hvertex
  have hpos : position < length := List.mem_range.mp hposition
  apply satisfies_positive_unit
  exact (coloringValuation_edgeAtom c ⟨root, hroot⟩
    ⟨start + position, by omega⟩ ⟨color, hcolorBound⟩).2 (hcolors position hpos)

theorem coloringValuation_satisfies_forbidRootInterval
    (c : EdgeColoring (Fin 15) ThreeColor)
    (root start length color : Nat)
    (hroot : root < 15) (hbound : start + length ≤ 15) (hcolorBound : color < 3)
    (hcolors : ∀ position (hpos : position < length),
      c ⟨root, hroot⟩ ⟨start + position, by omega⟩ ≠ ⟨color, hcolorBound⟩) :
    (coloringValuation c).satisfies_fmla
      ((interval start length).map (fun vertex =>
        [Sat.Literal.neg (edgeAtom root vertex color)])) := by
  constructor
  intro clause hclause
  simp only [List.mem_map] at hclause
  obtain ⟨vertex, hvertex, rfl⟩ := hclause
  simp only [interval, List.mem_map] at hvertex
  obtain ⟨position, hposition, rfl⟩ := hvertex
  have hpos : position < length := List.mem_range.mp hposition
  apply satisfies_negative_unit
  intro hv
  apply hcolors position hpos
  exact (coloringValuation_edgeAtom c ⟨root, hroot⟩
    ⟨start + position, by omega⟩ ⟨color, hcolorBound⟩).1 hv

theorem coloringValuation_satisfies_selectRootPrefix
    (c : EdgeColoring (Fin 15) ThreeColor)
    (root start length selected color : Nat)
    (hroot : root < 15) (hbound : start + length ≤ 15) (hcolorBound : color < 3)
    (hcolors : ∀ position (hpos : position < length),
      (position < selected →
        c ⟨root, hroot⟩ ⟨start + position, by omega⟩ = ⟨color, hcolorBound⟩) ∧
      (¬position < selected →
        c ⟨root, hroot⟩ ⟨start + position, by omega⟩ ≠ ⟨color, hcolorBound⟩)) :
    (coloringValuation c).satisfies_fmla
      (selectRootPrefix root start length selected color) := by
  constructor
  intro clause hclause
  simp only [selectRootPrefix, List.mem_map] at hclause
  obtain ⟨position, hposition, rfl⟩ := hclause
  have hpos : position < length := List.mem_range.mp hposition
  by_cases hs : position < selected
  · simp only [hs, if_true]
    apply satisfies_positive_unit
    exact (coloringValuation_edgeAtom c ⟨root, hroot⟩
      ⟨start + position, by omega⟩ ⟨color, hcolorBound⟩).2
        ((hcolors position hpos).1 hs)
  · simp only [hs, if_false]
    apply satisfies_negative_unit
    intro hv
    apply (hcolors position hpos).2 hs
    exact (coloringValuation_edgeAtom c ⟨root, hroot⟩
      ⟨start + position, by omega⟩ ⟨color, hcolorBound⟩).1 hv

theorem coloringValuation_satisfies_colorRootPrefix
    (c : EdgeColoring (Fin 15) ThreeColor)
    (root start length selected firstColor secondColor : Nat)
    (hroot : root < 15) (hbound : start + length ≤ 15)
    (hfirst : firstColor < 3) (hsecond : secondColor < 3)
    (hcolors : ∀ position (hpos : position < length),
      c ⟨root, hroot⟩ ⟨start + position, by omega⟩ =
        (if _hp : position < selected then ⟨firstColor, hfirst⟩
         else ⟨secondColor, hsecond⟩)) :
    (coloringValuation c).satisfies_fmla
      (colorRootPrefix root start length selected firstColor secondColor) := by
  constructor
  intro clause hclause
  simp only [colorRootPrefix, List.mem_map] at hclause
  obtain ⟨position, hposition, rfl⟩ := hclause
  have hpos : position < length := List.mem_range.mp hposition
  by_cases hs : position < selected
  · simp only [hs, if_true]
    apply satisfies_positive_unit
    exact (coloringValuation_edgeAtom c ⟨root, hroot⟩
      ⟨start + position, by omega⟩ ⟨firstColor, hfirst⟩).2 (by
        simpa [hs] using hcolors position hpos)
  · simp only [hs, if_false]
    apply satisfies_positive_unit
    exact (coloringValuation_edgeAtom c ⟨root, hroot⟩
      ⟨start + position, by omega⟩ ⟨secondColor, hsecond⟩).2 (by
        simpa [hs] using hcolors position hpos)

theorem normalizedBadK15_satisfies_base_leaf
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    let blueRed := (endpointCell d u v 1 0).card
    (coloringValuation (normalizedBadK15 d hd u v huv hedge hdu hdv)).satisfies_fmla
      (k15BadDeficientLeaf blueRed) := by
  dsimp only
  let c' := normalizedBadK15 d hd u v huv hedge hdu hdv
  let redFirst := (endpointCell d u v 0 1).card
  let blueRed := (endpointCell d u v 1 0).card
  let blueBlue := (endpointCell d u v 1 1).card
  rcases k15_endpoint_parameter_facts d hd u v huv hedge hdu hdv with
    ⟨ha, hr, hrb, hab, hlow, hcells⟩
  have hgood : NoMonochromaticTriangle c' :=
    normalizedBadK15_good d hd u v huv hedge hdu hdv
  have hbase : (coloringValuation c').satisfies_fmla k15BaseLiteral := by
    rw [k15BaseLiteral_eq]
    exact coloring_satisfies_goodColoringFmla c' hgood
  have hrootRed : (coloringValuation c').satisfies_fmla
      (setRootBlock 0 1 4 0) := by
    apply coloringValuation_satisfies_setRootBlock c' 0 1 4 0 (by omega) (by omega) (by omega)
    intro position hposition
    by_cases hz : position = 0
    · subst position
      simpa [c'] using normalizedBadK15_edge_zero_one d hd u v huv hedge hdu hdv
    · let x : Fin 15 := ⟨1 + position, by omega⟩
      have hx0 : x ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp [x] at this
      have hx1 : x ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp [x] at this
        omega
      have hcolors := normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1
      have hcond : 1 + position < 5 := by omega
      simpa [c', x, canonicalFirstColor, hcond] using hcolors.1
  have hrootBlue : (coloringValuation c').satisfies_fmla
      (setRootBlock 0 5 5 1) := by
    apply coloringValuation_satisfies_setRootBlock c' 0 5 5 1 (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨5 + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this
    have hx1 : x ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hcolors := normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1
    have hn5 : ¬5 + position < 5 := by omega
    have h10 : 5 + position < 10 := by omega
    simpa [c', x, canonicalFirstColor, hn5, h10] using hcolors.1
  have hrootGreen : (coloringValuation c').satisfies_fmla
      (setRootBlock 0 10 5 2) := by
    apply coloringValuation_satisfies_setRootBlock c' 0 10 5 2 (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨10 + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this
    have hx1 : x ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hcolors := normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1
    have hn5 : ¬10 + position < 5 := by omega
    have hn10 : ¬10 + position < 10 := by omega
    simpa [c', x, canonicalFirstColor, hn5, hn10] using hcolors.1
  have hforbid : (coloringValuation c').satisfies_fmla
      ((interval 2 3).map (fun vertex =>
        [Sat.Literal.neg (edgeAtom 1 vertex 0)])) := by
    apply coloringValuation_satisfies_forbidRootInterval c' 1 2 3 0
      (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨2 + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this
    have hx1 : x ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hcolors := normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1
    have hc2 : c' 1 x = canonicalSecondColor redFirst blueRed blueBlue x := by
      simpa [c', redFirst, blueRed, blueBlue] using hcolors.2
    intro hzero
    have hc2nat : c' ⟨1, by omega⟩ ⟨2 + position, by omega⟩ =
        canonicalSecondColor redFirst blueRed blueBlue x := by simpa [x] using hc2
    have hz : canonicalSecondColor redFirst blueRed blueBlue x = 0 :=
      hc2nat.symm.trans hzero
    have hlt5 : 2 + position < 5 := by omega
    by_cases hinner : 2 + position < 2 + redFirst
    · have hone : canonicalSecondColor redFirst blueRed blueBlue x = 1 := by
        simp [canonicalSecondColor, x, hlt5, hinner]
      exact (by decide : (1 : ThreeColor) ≠ 0) (hone.symm.trans hz)
    · have htwo : canonicalSecondColor redFirst blueRed blueBlue x = 2 := by
        simp [canonicalSecondColor, x, hlt5, hinner]
      exact (by decide : (2 : ThreeColor) ≠ 0) (htwo.symm.trans hz)
  have hselectBlue : (coloringValuation c').satisfies_fmla
      (selectRootPrefix 1 5 5 blueRed 0) := by
    apply coloringValuation_satisfies_selectRootPrefix c' 1 5 5 blueRed 0
      (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨5 + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this
    have hx1 : x ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hcolors := normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1
    have hc2 : c' 1 x = canonicalSecondColor redFirst blueRed blueBlue x := by
      simpa [c', redFirst, blueRed, blueBlue] using hcolors.2
    have hn5 : ¬5 + position < 5 := by omega
    have hlt10 : 5 + position < 10 := by omega
    constructor
    · intro hs
      have hcond : 5 + position < 5 + blueRed := by omega
      simpa [canonicalSecondColor, x, hn5, hlt10, hcond] using hc2
    · intro hs
      have hcond : ¬5 + position < 5 + blueRed := by omega
      intro hzero
      have hc2nat : c' ⟨1, by omega⟩ ⟨5 + position, by omega⟩ =
          canonicalSecondColor redFirst blueRed blueBlue x := by simpa [x] using hc2
      have hz : canonicalSecondColor redFirst blueRed blueBlue x = 0 :=
        hc2nat.symm.trans hzero
      by_cases hinner : 5 + position < 5 + blueRed + blueBlue
      · have hone : canonicalSecondColor redFirst blueRed blueBlue x = 1 := by
          simp [canonicalSecondColor, x, hn5, hlt10, hcond, hinner]
        exact (by decide : (1 : ThreeColor) ≠ 0) (hone.symm.trans hz)
      · have htwo : canonicalSecondColor redFirst blueRed blueBlue x = 2 := by
          simp [canonicalSecondColor, x, hn5, hlt10, hcond, hinner]
        exact (by decide : (2 : ThreeColor) ≠ 0) (htwo.symm.trans hz)
  have hselectGreen : (coloringValuation c').satisfies_fmla
      (selectRootPrefix 1 10 5 (3 - blueRed) 0) := by
    apply coloringValuation_satisfies_selectRootPrefix c' 1 10 5 (3 - blueRed) 0
      (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨10 + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this
    have hx1 : x ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hcolors := normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1
    have hc2 : c' 1 x = canonicalSecondColor redFirst blueRed blueBlue x := by
      simpa [c', redFirst, blueRed, blueBlue] using hcolors.2
    have hn5 : ¬10 + position < 5 := by omega
    have hn10 : ¬10 + position < 10 := by omega
    constructor
    · intro hs
      have hcond : 10 + position < 13 - blueRed := by omega
      simpa [canonicalSecondColor, x, hn5, hn10, hcond] using hc2
    · intro hs
      have hcond : ¬10 + position < 13 - blueRed := by omega
      intro hzero
      have hc2nat : c' ⟨1, by omega⟩ ⟨10 + position, by omega⟩ =
          canonicalSecondColor redFirst blueRed blueBlue x := by simpa [x] using hc2
      have hz : canonicalSecondColor redFirst blueRed blueBlue x = 0 :=
        hc2nat.symm.trans hzero
      by_cases hinner : 10 + position < 18 - blueRed - redFirst - blueBlue
      · have hone : canonicalSecondColor redFirst blueRed blueBlue x = 1 := by
          simp [canonicalSecondColor, x, hn5, hn10, hcond, hinner]
        exact (by decide : (1 : ThreeColor) ≠ 0) (hone.symm.trans hz)
      · have htwo : canonicalSecondColor redFirst blueRed blueBlue x = 2 := by
          simp [canonicalSecondColor, x, hn5, hn10, hcond, hinner]
        exact (by decide : (2 : ThreeColor) ≠ 0) (htwo.symm.trans hz)
  unfold k15BadDeficientLeaf
  have h01 := satisfies_fmla_append _ _ _ hbase hrootRed
  have h02 := satisfies_fmla_append _ _ _ h01 hrootBlue
  have h03 := satisfies_fmla_append _ _ _ h02 hrootGreen
  have h04 := satisfies_fmla_append _ _ _ h03 hforbid
  have h05 := satisfies_fmla_append _ _ _ h04 hselectBlue
  exact satisfies_fmla_append _ _ _ h05 hselectGreen

theorem normalizedBadK15_satisfies_refined_leaf
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) :
    let redFirst := (endpointCell d u v 0 1).card
    let blueRed := (endpointCell d u v 1 0).card
    let blueBlue := (endpointCell d u v 1 1).card
    (coloringValuation (normalizedBadK15 d hd u v huv hedge hdu hdv)).satisfies_fmla
      (k15BadDeficientRefined blueRed redFirst blueBlue) := by
  dsimp only
  let c' := normalizedBadK15 d hd u v huv hedge hdu hdv
  let redFirst := (endpointCell d u v 0 1).card
  let blueRed := (endpointCell d u v 1 0).card
  let blueBlue := (endpointCell d u v 1 1).card
  rcases k15_endpoint_parameter_facts d hd u v huv hedge hdu hdv with
    ⟨ha, hr, hrb, hab, hlow, hcells⟩
  have hbase := normalizedBadK15_satisfies_base_leaf d hd u v huv hedge hdu hdv
  have hfirst : (coloringValuation c').satisfies_fmla
      (colorRootPrefix 1 2 3 redFirst 1 2) := by
    apply coloringValuation_satisfies_colorRootPrefix c' 1 2 3 redFirst 1 2
      (by omega) (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨2 + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this
    have hx1 : x ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hc := (normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1).2
    have hc' : c' 1 x = canonicalSecondColor redFirst blueRed blueBlue x := by
      simpa [c', redFirst, blueRed, blueBlue] using hc
    have hlt5 : 2 + position < 5 := by omega
    by_cases hs : position < redFirst
    · have hinner : 2 + position < 2 + redFirst := by omega
      simpa [hs, canonicalSecondColor, x, hlt5, hinner] using hc'
    · have hinner : ¬2 + position < 2 + redFirst := by omega
      simpa [hs, canonicalSecondColor, x, hlt5, hinner] using hc'
  have hsecond : (coloringValuation c').satisfies_fmla
      (colorRootPrefix 1 (5 + blueRed) (5 - blueRed) blueBlue 1 2) := by
    apply coloringValuation_satisfies_colorRootPrefix c' 1 (5 + blueRed)
      (5 - blueRed) blueBlue 1 2 (by omega) (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨5 + blueRed + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this
    have hx1 : x ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hc := (normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1).2
    have hc' : c' 1 x = canonicalSecondColor redFirst blueRed blueBlue x := by
      simpa [c', redFirst, blueRed, blueBlue] using hc
    have hn5 : ¬5 + blueRed + position < 5 := by omega
    have hlt10 : 5 + blueRed + position < 10 := by omega
    have hnred : ¬5 + blueRed + position < 5 + blueRed := by omega
    by_cases hs : position < blueBlue
    · have hinner : 5 + blueRed + position < 5 + blueRed + blueBlue := by omega
      simpa [hs, canonicalSecondColor, x, hn5, hlt10, hnred, hinner] using hc'
    · have hinner : ¬5 + blueRed + position < 5 + blueRed + blueBlue := by omega
      simpa [hs, canonicalSecondColor, x, hn5, hlt10, hnred, hinner] using hc'
  have hthird : (coloringValuation c').satisfies_fmla
      (colorRootPrefix 1 (13 - blueRed) (2 + blueRed)
        (5 - redFirst - blueBlue) 1 2) := by
    apply coloringValuation_satisfies_colorRootPrefix c' 1 (13 - blueRed)
      (2 + blueRed) (5 - redFirst - blueBlue) 1 2
      (by omega) (by omega) (by omega) (by omega)
    intro position hposition
    let x : Fin 15 := ⟨13 - blueRed + position, by omega⟩
    have hx0 : x ≠ 0 := by intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hx1 : x ≠ 1 := by intro h; have := congrArg Fin.val h; simp [x] at this; omega
    have hc := (normalizedBadK15_root_colors d hd u v huv hedge hdu hdv x hx0 hx1).2
    have hc' : c' 1 x = canonicalSecondColor redFirst blueRed blueBlue x := by
      simpa [c', redFirst, blueRed, blueBlue] using hc
    have hn5 : ¬13 - blueRed + position < 5 := by omega
    have hn10 : ¬13 - blueRed + position < 10 := by omega
    have hnred : ¬13 - blueRed + position < 13 - blueRed := by omega
    by_cases hs : position < 5 - redFirst - blueBlue
    · have hinner : 13 - blueRed + position <
          18 - blueRed - redFirst - blueBlue := by omega
      simpa [hs, canonicalSecondColor, x, hn5, hn10, hnred, hinner] using hc'
    · have hinner : ¬13 - blueRed + position <
          18 - blueRed - redFirst - blueBlue := by omega
      simpa [hs, canonicalSecondColor, x, hn5, hn10, hnred, hinner] using hc'
  unfold k15BadDeficientRefined
  have h01 := satisfies_fmla_append _ _ _ hbase hfirst
  have h02 := satisfies_fmla_append _ _ _ h01 hsecond
  exact satisfies_fmla_append _ _ _ h02 hthird

/-- The checked leaves rule out every arithmetically feasible normalized bad
endpoint matrix. -/
theorem no_normalized_bad_k15_edge
    (d : EdgeColoring (Fin 15) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 15) (huv : u ≠ v)
    (hedge : d u v = 0)
    (hdu : colorDegree d 0 u = 4) (hdv : colorDegree d 0 v = 4) : False := by
  let redFirst := (endpointCell d u v 0 1).card
  let blueRed := (endpointCell d u v 1 0).card
  let blueBlue := (endpointCell d u v 1 1).card
  rcases k15_endpoint_parameter_facts d hd u v huv hedge hdu hdv with
    ⟨ha, hr, hrb, hab, hlow, hcells⟩
  change redFirst ≤ 3 at ha
  change blueRed ≤ 3 at hr
  change blueRed + blueBlue ≤ 5 at hrb
  change redFirst + blueBlue ≤ 5 at hab
  change 3 ≤ blueRed + redFirst + blueBlue at hlow
  have hb : blueBlue ≤ 5 := by omega
  let c' := normalizedBadK15 d hd u v huv hedge hdu hdv
  have hbase : (coloringValuation c').satisfies_fmla
      (k15BadDeficientLeaf blueRed) := by
    simpa [c', blueRed] using
      normalizedBadK15_satisfies_base_leaf d hd u v huv hedge hdu hdv
  have hrefined : (coloringValuation c').satisfies_fmla
      (k15BadDeficientRefined blueRed redFirst blueBlue) := by
    simpa [c', blueRed, redFirst, blueBlue] using
      normalizedBadK15_satisfies_refined_leaf d hd u v huv hedge hdu hdv
  interval_cases blueRed
  · exact k15_deficient_split_0_unsat (coloringValuation c') hbase
  · interval_cases redFirst <;> interval_cases blueBlue
    all_goals first
      | exact k15_deficient_1_blue_0_2_3_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_0_3_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_0_4_1_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_1_1_3_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_1_2_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_1_3_1_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_1_4_0_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_2_0_3_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_2_1_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_2_2_1_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_2_3_0_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_3_0_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_3_1_1_unsat (coloringValuation c') hrefined
      | exact k15_deficient_1_blue_3_2_0_unsat (coloringValuation c') hrefined
      | omega
  · interval_cases redFirst <;> interval_cases blueBlue
    all_goals first
      | exact k15_deficient_2_blue_0_1_4_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_0_2_3_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_0_3_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_1_0_4_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_1_1_3_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_1_2_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_1_3_1_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_2_0_3_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_2_1_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_2_2_1_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_2_3_0_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_3_0_2_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_3_1_1_unsat (coloringValuation c') hrefined
      | exact k15_deficient_2_blue_3_2_0_unsat (coloringValuation c') hrefined
      | omega
  · exact k15_deficient_split_3_unsat (coloringValuation c') hbase

end K15LeafSemantics

/-- The finite LRAT leaves, together with the ordinary colour/vertex
normalization above, prove the deficient-edge rule for every good labelled
`K15`. -/
theorem deficientEdgeFree_of_checked_leaves
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) : DeficientEdgeFree c hc := by
  intro u v huv hsame hedgeOriginal
  let q := deficientColor15 c hc u
  let colorEquiv : ThreeColor ≃ ThreeColor := Equiv.swap q 0
  let d := mapEdgeColors c colorEquiv
  have hd : NoMonochromaticTriangle d := noMono_mapEdgeColors c colorEquiv hc
  have hinv : colorEquiv.symm 0 = q := by simp [colorEquiv]
  have hedge : d u v = 0 := by
    simp [d, colorEquiv, q, hedgeOriginal]
  have hdu : colorDegree d 0 u = 4 := by
    rw [colorDegree_mapEdgeColors, hinv]
    exact deficientColor15_degree c hc u
  have hdv : colorDegree d 0 v = 4 := by
    rw [colorDegree_mapEdgeColors, hinv]
    change colorDegree c (deficientColor15 c hc u) v = 4
    rw [hsame]
    exact deficientColor15_degree c hc v
  exact K15LeafSemantics.no_normalized_bad_k15_edge d hd u v huv hedge hdu hdv

/-- Unconditional certified extension of every critical good `K15` to a good
`K16`. -/
theorem extendCriticalK15_good_unconditional
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (extendCriticalK15 c hc) :=
  extendCriticalK15_good c hc (deficientEdgeFree_of_checked_leaves c hc)

#print axioms R4333.deficientEdgeFree_of_checked_leaves
#print axioms R4333.extendCriticalK15_good_unconditional

end R4333
