import R4333Lean.CatalogueBaseCNFLeavesK16Refined
import R4333Lean.CatalogueBaseCNFSemantics
import R4333Lean.ColorRelabel
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Certified common-neighbour rule for good three-colourings of `K16`

This file supplies the mathematical normalization between an arbitrary
non-colour edge and the small kernel-checked LRAT cubes in
`CatalogueBaseCNFLeavesK16Refined`.  No graph catalogue is used.
-/

namespace R4333

open FiniteColorCNF CatalogueBaseCNF

instance colorGraphDecidableRel {V C : Type*} [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (q : C) : DecidableRel (colorGraph c q).Adj := by
  intro u v
  change Decidable (u ≠ v ∧ c u v = q)
  infer_instance

/-- A finite key for a coarse two-endpoint partition.  The Boolean records
whether the second endpoint uses colour zero. -/
inductive K16CoarseKey where
  | first
  | second
  | cell (fromFirst : ThreeColor) (secondIsZero : Bool)
  deriving DecidableEq

def K16CoarseKey.firstColor? : K16CoarseKey → Option ThreeColor
  | .cell p _ => some p
  | _ => none

def K16CoarseKey.secondIsZero? : K16CoarseKey → Option Bool
  | .cell _ b => some b
  | _ => none

/-- A half-open interval of canonical K16 labels. -/
def fin16Interval (lo hi : Nat) : Finset (Fin 16) :=
  Finset.univ.filter fun i => lo ≤ i.val ∧ i.val < hi

@[simp] theorem mem_fin16Interval (lo hi : Nat) (i : Fin 16) :
    i ∈ fin16Interval lo hi ↔ lo ≤ i.val ∧ i.val < hi := by
  simp [fin16Interval]

theorem card_fin16Interval (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ 16) :
    (fin16Interval lo hi).card = hi - lo := by
  let e : {i // i ∈ fin16Interval lo hi} ≃ Fin (hi - lo) :=
    { toFun := fun i => ⟨i.1.val - lo, by
        have hi_mem := (mem_fin16Interval lo hi i).mp i.2
        omega⟩
      invFun := fun j => ⟨⟨lo + j.val, by omega⟩, by
        apply (mem_fin16Interval lo hi _).mpr
        change lo ≤ lo + j.val ∧ lo + j.val < hi
        omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        change lo + (i.1.val - lo) = i.1.val
        have hi_mem := (mem_fin16Interval lo hi i).mp i.2
        omega
      right_inv := by
        intro j
        apply Fin.ext
        change (lo + j.val) - lo = j.val
        omega }
  rw [← Fintype.card_coe]
  simpa using Fintype.card_congr e

/-- Canonical labels for a coarse endpoint partition with three zero-column
counts. -/
def k16CanonicalCoarseKey (n0 n1 n2 : Nat) (i : Fin 16) : K16CoarseKey :=
  if i.val = 0 then .first
  else if i.val = 1 then .second
  else if i.val < 2 + n0 then .cell 0 true
  else if i.val < 7 then .cell 0 false
  else if i.val < 7 + n1 then .cell 1 true
  else if i.val < 11 then .cell 1 false
  else if i.val < 11 + n2 then .cell 2 true
  else .cell 2 false

theorem k16CanonicalCoarseKey_root0_block
    (n0 n1 n2 start length : Nat) (p : ThreeColor)
    (hn0 : n0 ≤ 5) (hn1 : n1 ≤ 4) (_hn2 : n2 ≤ 5)
    (hblock : (start, length, p) = (2, 5, 0) ∨
      (start, length, p) = (7, 4, 1) ∨
      (start, length, p) = (11, 5, 2))
    (position : Nat) (hposition : position < length)
    (hlabel : start + position < 16) :
    (k16CanonicalCoarseKey n0 n1 n2 ⟨start + position, hlabel⟩).firstColor? =
      some p := by
  rcases hblock with h | h | h
  all_goals
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [k16CanonicalCoarseKey, K16CoarseKey.firstColor?]
    all_goals split_ifs
    all_goals simp_all
    all_goals omega

theorem k16CanonicalCoarseKey_second_zero
    (n0 n1 n2 start length selected : Nat)
    (hn0 : n0 ≤ 5) (hn1 : n1 ≤ 4) (hn2 : n2 ≤ 5)
    (hblock : (start, length, selected) = (2, 5, n0) ∨
      (start, length, selected) = (7, 4, n1) ∨
      (start, length, selected) = (11, 5, n2))
    (position : Nat) (hposition : position < length)
    (hlabel : start + position < 16) :
    (k16CanonicalCoarseKey n0 n1 n2
      ⟨start + position, hlabel⟩).secondIsZero? =
      some (decide (position < selected)) := by
  rcases hblock with h | h | h
  all_goals
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [k16CanonicalCoarseKey, K16CoarseKey.secondIsZero?]
    all_goals split_ifs
    all_goals simp_all
    all_goals omega

/-- Actual coarse endpoint partition of a colouring. -/
def k16ActualCoarseKey (d : EdgeColoring (Fin 16) ThreeColor)
    (u v x : Fin 16) : K16CoarseKey :=
  if x = u then .first
  else if x = v then .second
  else .cell (d u x) (d v x = 0)

/-- The finite fibre of a key function, represented as a finset. -/
def keyFiber {A K : Type*} [Fintype A] [DecidableEq K]
    (f : A → K) (k : K) : Finset A :=
  Finset.univ.filter fun a => f a = k

@[simp] theorem mem_keyFiber {A K : Type*} [Fintype A] [DecidableEq K]
    (f : A → K) (k : K) (a : A) :
    a ∈ keyFiber f k ↔ f a = k := by
  simp [keyFiber]

theorem card_keyFiber {A K : Type*} [Fintype A] [DecidableEq K]
    (f : A → K) (k : K) :
    Fintype.card {a // f a = k} = (keyFiber f k).card := by
  let e : {a // f a = k} ≃ {a // a ∈ keyFiber f k} :=
    { toFun := fun a => ⟨a, (mem_keyFiber f k a).2 a.2⟩
      invFun := fun a => ⟨a, (mem_keyFiber f k a).1 a.2⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  rw [← Fintype.card_coe]
  exact Fintype.card_congr e

theorem k16CanonicalCoarseKey_first_fiber (n0 n1 n2 : Nat) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) .first = {0} := by
  ext i
  simp only [mem_keyFiber, Finset.mem_singleton]
  simp [k16CanonicalCoarseKey]
  split_ifs <;> simp_all

theorem k16CanonicalCoarseKey_second_fiber (n0 n1 n2 : Nat) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) .second = {1} := by
  ext i
  simp only [mem_keyFiber, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h0 : i.val = 0
    · simp [k16CanonicalCoarseKey, h0] at h
    by_cases h1 : i.val = 1
    · exact Fin.ext h1
    · simp only [k16CanonicalCoarseKey, h0, h1, ↓reduceIte] at h
      split_ifs at h
  · intro h
    subst i
    simp [k16CanonicalCoarseKey]

theorem k16CanonicalCoarseKey_0_true_fiber (n0 n1 n2 : Nat) (_h0 : n0 ≤ 5) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) (.cell 0 true) =
      fin16Interval 2 (2 + n0) := by
  ext i
  simp only [mem_keyFiber, mem_fin16Interval]
  simp [k16CanonicalCoarseKey]
  split_ifs
  all_goals simp_all
  all_goals omega

theorem k16CanonicalCoarseKey_0_false_fiber (n0 n1 n2 : Nat) (h0 : n0 ≤ 5) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) (.cell 0 false) =
      fin16Interval (2 + n0) 7 := by
  ext i
  simp only [mem_keyFiber, mem_fin16Interval]
  simp [k16CanonicalCoarseKey]
  split_ifs
  all_goals simp_all
  all_goals omega

theorem k16CanonicalCoarseKey_1_true_fiber (n0 n1 n2 : Nat)
    (h0 : n0 ≤ 5) (_h1 : n1 ≤ 4) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) (.cell 1 true) =
      fin16Interval 7 (7 + n1) := by
  ext i
  simp only [mem_keyFiber, mem_fin16Interval]
  simp [k16CanonicalCoarseKey]
  split_ifs
  all_goals simp_all
  all_goals omega

theorem k16CanonicalCoarseKey_1_false_fiber (n0 n1 n2 : Nat)
    (h0 : n0 ≤ 5) (h1 : n1 ≤ 4) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) (.cell 1 false) =
      fin16Interval (7 + n1) 11 := by
  ext i
  simp only [mem_keyFiber, mem_fin16Interval]
  simp [k16CanonicalCoarseKey]
  split_ifs <;> simp_all <;> omega

theorem k16CanonicalCoarseKey_2_true_fiber (n0 n1 n2 : Nat)
    (h0 : n0 ≤ 5) (h1 : n1 ≤ 4) (_h2 : n2 ≤ 5) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) (.cell 2 true) =
      fin16Interval 11 (11 + n2) := by
  ext i
  simp only [mem_keyFiber, mem_fin16Interval]
  simp [k16CanonicalCoarseKey]
  split_ifs <;> simp_all <;> omega

theorem k16CanonicalCoarseKey_2_false_fiber (n0 n1 n2 : Nat)
    (h0 : n0 ≤ 5) (h1 : n1 ≤ 4) (h2 : n2 ≤ 5) :
    keyFiber (k16CanonicalCoarseKey n0 n1 n2) (.cell 2 false) =
      fin16Interval (11 + n2) 16 := by
  ext i
  simp only [mem_keyFiber, mem_fin16Interval]
  simp [k16CanonicalCoarseKey]
  split_ifs <;> simp_all <;> omega

/-- Vertices other than the selected endpoints. -/
def k16AwayFrom (u v : Fin 16) : Finset (Fin 16) :=
  (Finset.univ.erase u).erase v

/-- A cell of the endpoint-colour matrix. -/
def k16EndpointCell (d : EdgeColoring (Fin 16) ThreeColor)
    (u v : Fin 16) (p q : ThreeColor) : Finset (Fin 16) :=
  (k16AwayFrom u v).filter fun x => d u x = p ∧ d v x = q

/-- A row of the endpoint-colour matrix. -/
def k16EndpointRow (d : EdgeColoring (Fin 16) ThreeColor)
    (u v : Fin 16) (p : ThreeColor) : Finset (Fin 16) :=
  (k16AwayFrom u v).filter fun x => d u x = p

/-- A column of the endpoint-colour matrix. -/
def k16EndpointColumn (d : EdgeColoring (Fin 16) ThreeColor)
    (u v : Fin 16) (q : ThreeColor) : Finset (Fin 16) :=
  (k16AwayFrom u v).filter fun x => d v x = q

/-- The nonzero part of one endpoint row. -/
def k16EndpointNonzeroCell (d : EdgeColoring (Fin 16) ThreeColor)
    (u v : Fin 16) (p : ThreeColor) : Finset (Fin 16) :=
  (k16EndpointRow d u v p).filter fun x => d v x ≠ 0

theorem k16EndpointRow_eq_erase_neighborhood
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (p : ThreeColor) :
    k16EndpointRow d u v p = (colorNeighborhood d p u).erase v := by
  ext x
  simp [k16EndpointRow, k16AwayFrom, colorNeighborhood, and_assoc,
    and_left_comm, and_comm]

theorem k16EndpointColumn_eq_erase_neighborhood
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (q : ThreeColor) :
    k16EndpointColumn d u v q = (colorNeighborhood d q v).erase u := by
  ext x
  simp [k16EndpointColumn, k16AwayFrom, colorNeighborhood, and_assoc,
    and_comm]

theorem k16EndpointColumn_card_eq_sum_cells
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (q : ThreeColor) :
    (k16EndpointColumn d u v q).card =
      (k16EndpointCell d u v 0 q).card +
      ((k16EndpointCell d u v 1 q).card +
        (k16EndpointCell d u v 2 q).card) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := k16EndpointColumn d u v q) (t := Finset.univ)
    (f := fun x => d u x) (by simp)
  simpa [Fin.sum_univ_succ, k16EndpointColumn, k16EndpointCell,
    Finset.filter_filter, and_assoc, and_left_comm, and_comm] using h

theorem k16EndpointRow_card
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (huv : u ≠ v)
    (hedge : d u v = 1) (p : ThreeColor) :
    (k16EndpointRow d u v p).card = if p = 1 then 4 else 5 := by
  rw [k16EndpointRow_eq_erase_neighborhood]
  have hdegree := threeColor_degree_eq_five_at_16 d hd p u
  change (colorNeighborhood d p u).card = 5 at hdegree
  by_cases hp : p = 1
  · subst p
    have hmem : v ∈ colorNeighborhood d 1 u := by
      simp [huv.symm, hedge]
    rw [Finset.card_erase_of_mem hmem, hdegree]
    norm_num
  · have hnot : v ∉ colorNeighborhood d p u := by
      simp only [mem_colorNeighborhood, not_and_or]
      exact Or.inr (by rw [hedge]; exact Ne.symm hp)
    rw [Finset.erase_eq_of_notMem hnot]
    simp only [hp]
    exact hdegree

theorem k16EndpointColumn_zero_card
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (_huv : u ≠ v)
    (hedge : d u v = 1) :
    (k16EndpointColumn d u v 0).card = 5 := by
  rw [k16EndpointColumn_eq_erase_neighborhood]
  have hnot : u ∉ colorNeighborhood d 0 v := by
    simp only [mem_colorNeighborhood, not_and_or]
    exact Or.inr (by simp [d.color_symm, hedge])
  rw [Finset.erase_eq_of_notMem hnot]
  exact threeColor_degree_eq_five_at_16 d hd 0 v

theorem k16ActualCoarseKey_first_fiber
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16) (huv : u ≠ v) :
    keyFiber (k16ActualCoarseKey d u v) .first = {u} := by
  ext x
  simp only [mem_keyFiber, Finset.mem_singleton]
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    simp [k16ActualCoarseKey, hxu, hxv, huv] at *

theorem k16ActualCoarseKey_second_fiber
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16) (huv : u ≠ v) :
    keyFiber (k16ActualCoarseKey d u v) .second = {v} := by
  ext x
  simp only [mem_keyFiber, Finset.mem_singleton]
  by_cases hxu : x = u
  · subst x
    simp [k16ActualCoarseKey, huv]
  · simp [k16ActualCoarseKey, hxu]

theorem k16ActualCoarseKey_true_fiber
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (p : ThreeColor) :
    keyFiber (k16ActualCoarseKey d u v) (.cell p true) =
      k16EndpointCell d u v p 0 := by
  ext x
  simp only [mem_keyFiber]
  by_cases hxu : x = u
  · subst x
    simp [k16ActualCoarseKey, k16EndpointCell, k16AwayFrom]
  by_cases hxv : x = v
  · subst x
    simp [k16ActualCoarseKey, k16EndpointCell, k16AwayFrom, hxu]
  by_cases hvx : d v x = 0 <;>
    simp [k16ActualCoarseKey, k16EndpointCell, k16AwayFrom,
      hxu, hxv, hvx, and_comm]

theorem k16ActualCoarseKey_false_fiber
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (p : ThreeColor) :
    keyFiber (k16ActualCoarseKey d u v) (.cell p false) =
      k16EndpointNonzeroCell d u v p := by
  ext x
  simp only [mem_keyFiber]
  by_cases hxu : x = u
  · subst x
    simp [k16ActualCoarseKey, k16EndpointNonzeroCell, k16EndpointRow,
      k16AwayFrom]
  by_cases hxv : x = v
  · subst x
    simp [k16ActualCoarseKey, k16EndpointNonzeroCell, k16EndpointRow,
      k16AwayFrom, hxu]
  by_cases hvx : d v x = 0 <;>
    simp [k16ActualCoarseKey, k16EndpointNonzeroCell, k16EndpointRow,
      k16AwayFrom, hxu, hxv, hvx, and_comm]

theorem k16EndpointCell_zero_add_nonzero
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (p : ThreeColor) :
    (k16EndpointCell d u v p 0).card +
      (k16EndpointNonzeroCell d u v p).card =
        (k16EndpointRow d u v p).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := k16EndpointRow d u v p) (p := fun x => d v x = 0)
  simpa [k16EndpointCell, k16EndpointNonzeroCell, k16EndpointRow,
    k16AwayFrom, Finset.filter_filter, and_assoc, and_left_comm, and_comm]
    using h

/-- Equal finite fibre sizes give an equivalence that preserves the fibre
key. -/
noncomputable def equivOfFiberCardEq {A B K : Type*}
    [Fintype A] [Fintype B] [DecidableEq K]
    (f : A → K) (g : B → K)
    (h : ∀ k, Fintype.card {a // f a = k} =
      Fintype.card {b // g b = k}) : A ≃ B :=
  Equiv.ofFiberEquiv fun k => Fintype.equivOfCardEq (h k)

theorem equivOfFiberCardEq_map {A B K : Type*}
    [Fintype A] [Fintype B] [DecidableEq K]
    (f : A → K) (g : B → K)
    (h : ∀ k, Fintype.card {a // f a = k} =
      Fintype.card {b // g b = k}) (a : A) :
    g (equivOfFiberCardEq f g h a) = f a := by
  exact Equiv.ofFiberEquiv_map _ _

private theorem k16_threeColor_cases (p : ThreeColor) :
    p = 0 ∨ p = 1 ∨ p = 2 := by
  fin_cases p <;> simp

/-- The coarse normalizing equivalence.  It fixes the selected endpoints at
canonical labels zero and one, sorts the first endpoint's colour classes,
and within each class puts the second endpoint's zero-colour neighbours
first. -/
theorem exists_k16CoarseRelabel
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (huv : u ≠ v)
    (hedge : d u v = 1) :
    ∃ e : Fin 16 ≃ Fin 16,
      e 0 = u ∧ e 1 = v ∧
      ∀ i, k16ActualCoarseKey d u v (e i) =
        k16CanonicalCoarseKey
          (k16EndpointCell d u v 0 0).card
          (k16EndpointCell d u v 1 0).card
          (k16EndpointCell d u v 2 0).card i := by
  let n0 := (k16EndpointCell d u v 0 0).card
  let n1 := (k16EndpointCell d u v 1 0).card
  let n2 := (k16EndpointCell d u v 2 0).card
  have hrow0 : (k16EndpointRow d u v (0 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (0 : ThreeColor)
  have hrow1 : (k16EndpointRow d u v (1 : ThreeColor)).card = 4 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (1 : ThreeColor)
  have hrow2 : (k16EndpointRow d u v (2 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (2 : ThreeColor)
  have hpart0 := k16EndpointCell_zero_add_nonzero d u v (0 : ThreeColor)
  have hpart1 := k16EndpointCell_zero_add_nonzero d u v (1 : ThreeColor)
  have hpart2 := k16EndpointCell_zero_add_nonzero d u v (2 : ThreeColor)
  have hn0 : n0 ≤ 5 := by dsimp [n0]; omega
  have hn1 : n1 ≤ 4 := by dsimp [n1]; omega
  have hn2 : n2 ≤ 5 := by dsimp [n2]; omega
  have hfibers : ∀ key,
      Fintype.card {i // k16CanonicalCoarseKey n0 n1 n2 i = key} =
        Fintype.card {x // k16ActualCoarseKey d u v x = key} := by
    intro key
    rw [card_keyFiber, card_keyFiber]
    cases key with
    | first =>
        rw [k16CanonicalCoarseKey_first_fiber,
          k16ActualCoarseKey_first_fiber d u v huv]
        simp
    | second =>
        rw [k16CanonicalCoarseKey_second_fiber,
          k16ActualCoarseKey_second_fiber d u v huv]
        simp
    | cell p isZero =>
        rcases k16_threeColor_cases p with hp | hp | hp
        · subst p
          cases isZero
          · rw [k16CanonicalCoarseKey_0_false_fiber n0 n1 n2 hn0,
            k16ActualCoarseKey_false_fiber]
            rw [card_fin16Interval (2 + n0) 7 (by omega) (by omega)]
            dsimp [n0] at *
            omega
          · rw [k16CanonicalCoarseKey_0_true_fiber n0 n1 n2 hn0,
              k16ActualCoarseKey_true_fiber]
            rw [card_fin16Interval 2 (2 + n0) (by omega) (by omega)]
            simp [n0]
        · subst p
          cases isZero
          · rw [k16CanonicalCoarseKey_1_false_fiber n0 n1 n2 hn0 hn1,
              k16ActualCoarseKey_false_fiber]
            rw [card_fin16Interval (7 + n1) 11 (by omega) (by omega)]
            dsimp [n1] at *
            omega
          · rw [k16CanonicalCoarseKey_1_true_fiber n0 n1 n2 hn0 hn1,
              k16ActualCoarseKey_true_fiber]
            rw [card_fin16Interval 7 (7 + n1) (by omega) (by omega)]
            simp [n1]
        · subst p
          cases isZero
          · rw [k16CanonicalCoarseKey_2_false_fiber n0 n1 n2 hn0 hn1 hn2,
              k16ActualCoarseKey_false_fiber]
            rw [card_fin16Interval (11 + n2) 16 (by omega) (by omega)]
            dsimp [n2] at *
            omega
          · rw [k16CanonicalCoarseKey_2_true_fiber n0 n1 n2 hn0 hn1 hn2,
              k16ActualCoarseKey_true_fiber]
            rw [card_fin16Interval 11 (11 + n2) (by omega) (by omega)]
            simp [n2]
  let e := equivOfFiberCardEq
    (k16CanonicalCoarseKey n0 n1 n2) (k16ActualCoarseKey d u v) hfibers
  refine ⟨e, ?_, ?_, ?_⟩
  · have hkey := equivOfFiberCardEq_map
      (k16CanonicalCoarseKey n0 n1 n2) (k16ActualCoarseKey d u v)
      hfibers (0 : Fin 16)
    have hactual : k16ActualCoarseKey d u v (e 0) = .first := by
      simpa [e, k16CanonicalCoarseKey] using hkey
    have hmem : e 0 ∈ keyFiber (k16ActualCoarseKey d u v) .first :=
      (mem_keyFiber _ _ _).2 hactual
    rw [k16ActualCoarseKey_first_fiber d u v huv] at hmem
    simpa using hmem
  · have hkey := equivOfFiberCardEq_map
      (k16CanonicalCoarseKey n0 n1 n2) (k16ActualCoarseKey d u v)
      hfibers (1 : Fin 16)
    have hactual : k16ActualCoarseKey d u v (e 1) = .second := by
      simpa [e, k16CanonicalCoarseKey] using hkey
    have hmem : e 1 ∈ keyFiber (k16ActualCoarseKey d u v) .second :=
      (mem_keyFiber _ _ _).2 hactual
    rw [k16ActualCoarseKey_second_fiber d u v huv] at hmem
    simpa using hmem
  · intro i
    simpa [e, n0, n1, n2] using
      (equivOfFiberCardEq_map
        (k16CanonicalCoarseKey n0 n1 n2) (k16ActualCoarseKey d u v)
        hfibers i)

/-! ## Semantics of the three normalization gadgets -/

theorem coloring_satisfies_setRootBlock16
    (c : EdgeColoring (Fin 16) ThreeColor)
    (root start length color : Nat)
    (hroot : root < 16) (hbound : start + length ≤ 16)
    (hcolor : color < 3)
    (hcolors : ∀ position (hposition : position < length),
      c ⟨root, hroot⟩ ⟨start + position, by omega⟩ = ⟨color, hcolor⟩) :
    (coloringValuation c).satisfies_fmla
      (setRootBlock root start length color) := by
  constructor
  intro clause hclause
  simp only [setRootBlock, List.mem_map] at hclause
  obtain ⟨vertex, hvertex, rfl⟩ := hclause
  simp only [interval, List.mem_map] at hvertex
  obtain ⟨position, hposition, rfl⟩ := hvertex
  have hp : position < length := List.mem_range.mp hposition
  exact (satisfies_pos_unit
    ((coloringValuation_edgeAtom c ⟨root, hroot⟩
      ⟨start + position, by omega⟩ ⟨color, hcolor⟩).2
        (hcolors position hp))).prop _ (List.Mem.head _)

theorem coloring_satisfies_selectRootPrefix16
    (c : EdgeColoring (Fin 16) ThreeColor)
    (root start length selected color : Nat)
    (hroot : root < 16) (hbound : start + length ≤ 16)
    (hcolor : color < 3)
    (hcolors : ∀ position (hposition : position < length),
      (position < selected →
        c ⟨root, hroot⟩ ⟨start + position, by omega⟩ = ⟨color, hcolor⟩) ∧
      (¬ position < selected →
        c ⟨root, hroot⟩ ⟨start + position, by omega⟩ ≠ ⟨color, hcolor⟩)) :
    (coloringValuation c).satisfies_fmla
      (selectRootPrefix root start length selected color) := by
  constructor
  intro clause hclause
  simp only [selectRootPrefix, List.mem_map] at hclause
  obtain ⟨position, hposition, rfl⟩ := hclause
  have hp : position < length := List.mem_range.mp hposition
  by_cases hs : position < selected
  · simp only [hs, if_true]
    exact (satisfies_pos_unit
      ((coloringValuation_edgeAtom c ⟨root, hroot⟩
        ⟨start + position, by omega⟩ ⟨color, hcolor⟩).2
          ((hcolors position hp).1 hs))).prop _ (List.Mem.head _)
  · simp only [hs, if_false]
    exact (satisfies_neg_unit (fun hv => (hcolors position hp).2 hs
      ((coloringValuation_edgeAtom c ⟨root, hroot⟩
        ⟨start + position, by omega⟩ ⟨color, hcolor⟩).1 hv))).prop _
          (List.Mem.head _)

theorem coloring_satisfies_colorRootPrefix16
    (c : EdgeColoring (Fin 16) ThreeColor)
    (root start length selected firstColor secondColor : Nat)
    (hroot : root < 16) (hbound : start + length ≤ 16)
    (hfirst : firstColor < 3) (hsecond : secondColor < 3)
    (hcolors : ∀ position (hposition : position < length),
      c ⟨root, hroot⟩ ⟨start + position, by omega⟩ =
        (if position < selected then ⟨firstColor, hfirst⟩
         else ⟨secondColor, hsecond⟩)) :
    (coloringValuation c).satisfies_fmla
      (colorRootPrefix root start length selected firstColor secondColor) := by
  constructor
  intro clause hclause
  simp only [colorRootPrefix, List.mem_map] at hclause
  obtain ⟨position, hposition, rfl⟩ := hclause
  have hp : position < length := List.mem_range.mp hposition
  by_cases hs : position < selected
  · simp only [hs, if_true]
    exact (satisfies_pos_unit
      ((coloringValuation_edgeAtom c ⟨root, hroot⟩
        ⟨start + position, by omega⟩ ⟨firstColor, hfirst⟩).2
          (by simpa [hs] using hcolors position hp))).prop _ (List.Mem.head _)
  · simp only [hs, if_false]
    exact (satisfies_pos_unit
      ((coloringValuation_edgeAtom c ⟨root, hroot⟩
        ⟨start + position, by omega⟩ ⟨secondColor, hsecond⟩).2
          (by simpa [hs] using hcolors position hp))).prop _ (List.Mem.head _)

/-! ## The coarse normalized leaf -/

theorem exists_coloring_satisfying_k16BadCommonLeaf
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (huv : u ≠ v)
    (hedge : d u v = 1) :
    ∃ c' : EdgeColoring (Fin 16) ThreeColor,
      (coloringValuation c').satisfies_fmla
        (k16BadCommonLeaf
          (k16EndpointCell d u v 0 0).card
          (k16EndpointCell d u v 1 0).card) := by
  let n0 := (k16EndpointCell d u v 0 0).card
  let n1 := (k16EndpointCell d u v 1 0).card
  let n2 := (k16EndpointCell d u v 2 0).card
  have hrow0 : (k16EndpointRow d u v (0 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (0 : ThreeColor)
  have hrow1 : (k16EndpointRow d u v (1 : ThreeColor)).card = 4 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (1 : ThreeColor)
  have hrow2 : (k16EndpointRow d u v (2 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (2 : ThreeColor)
  have hpart0 := k16EndpointCell_zero_add_nonzero d u v (0 : ThreeColor)
  have hpart1 := k16EndpointCell_zero_add_nonzero d u v (1 : ThreeColor)
  have hpart2 := k16EndpointCell_zero_add_nonzero d u v (2 : ThreeColor)
  have hn0 : n0 ≤ 5 := by dsimp [n0]; omega
  have hn1 : n1 ≤ 4 := by dsimp [n1]; omega
  have hn2 : n2 ≤ 5 := by dsimp [n2]; omega
  have hcolumn := k16EndpointColumn_card_eq_sum_cells d u v (0 : ThreeColor)
  have hcolumnCard := k16EndpointColumn_zero_card d hd u v huv hedge
  have hsum : n0 + (n1 + n2) = 5 := by
    dsimp [n0, n1, n2]
    omega
  have hn2eq : 5 - n0 - n1 = n2 := by omega
  rcases exists_k16CoarseRelabel d hd u v huv hedge with
    ⟨e, he0, he1, hkey⟩
  let c' := relabelVertices d e
  have hgood : NoMonochromaticTriangle c' :=
    noMono_relabelVertices d e hd
  have hbase : (coloringValuation c').satisfies_fmla k16BaseLiteral :=
    coloring_satisfies_k16BaseLiteral c' hgood
  have hedgeUnit : (coloringValuation c').satisfies_fmla (setEdge 0 1 1) := by
    apply coloring_satisfies_setEdge c' (by omega) (by omega) (by omega)
    simpa [c', he0, he1] using hedge
  have rootBlock (start length : Nat) (p : ThreeColor)
      (hblock : (start, length, p) = (2, 5, 0) ∨
        (start, length, p) = (7, 4, 1) ∨
        (start, length, p) = (11, 5, 2))
      (hbound : start + length ≤ 16) :
      (coloringValuation c').satisfies_fmla
        (setRootBlock 0 start length p.val) := by
    apply coloring_satisfies_setRootBlock16 c' 0 start length p.val
      (by omega) hbound p.isLt
    intro position hposition
    let i : Fin 16 := ⟨start + position, by omega⟩
    have hstart : 2 ≤ start := by
      rcases hblock with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        rcases h with ⟨rfl, rfl, rfl⟩ <;> omega
    have hi0 : i ≠ 0 := by
      intro hi
      have := congrArg Fin.val hi
      dsimp [i] at this
      omega
    have hi1 : i ≠ 1 := by
      intro hi
      have := congrArg Fin.val hi
      dsimp [i] at this
      omega
    have heiu : e i ≠ u := by rw [← he0]; exact e.injective.ne hi0
    have heiv : e i ≠ v := by rw [← he1]; exact e.injective.ne hi1
    have hprojection := congrArg K16CoarseKey.firstColor? (hkey i)
    have hcanonical := k16CanonicalCoarseKey_root0_block
      n0 n1 n2 start length p hn0 hn1 hn2 hblock position hposition i.isLt
    rw [hcanonical] at hprojection
    simpa [c', i, he0, k16ActualCoarseKey, heiu, heiv,
      K16CoarseKey.firstColor?] using hprojection
  have hroot0 := rootBlock 2 5 (0 : ThreeColor) (Or.inl rfl) (by omega)
  have hroot1 := rootBlock 7 4 (1 : ThreeColor) (Or.inr (Or.inl rfl)) (by omega)
  have hroot2 := rootBlock 11 5 (2 : ThreeColor) (Or.inr (Or.inr rfl)) (by omega)
  have zeroPrefix (start length selected : Nat)
      (hblock : (start, length, selected) = (2, 5, n0) ∨
        (start, length, selected) = (7, 4, n1) ∨
        (start, length, selected) = (11, 5, n2))
      (hbound : start + length ≤ 16) :
      (coloringValuation c').satisfies_fmla
        (selectRootPrefix 1 start length selected 0) := by
    apply coloring_satisfies_selectRootPrefix16 c' 1 start length selected 0
      (by omega) hbound (by omega)
    intro position hposition
    let i : Fin 16 := ⟨start + position, by omega⟩
    have hstart : 2 ≤ start := by
      rcases hblock with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        rcases h with ⟨rfl, rfl, rfl⟩ <;> omega
    have hi0 : i ≠ 0 := by
      intro hi
      have := congrArg Fin.val hi
      dsimp [i] at this
      omega
    have hi1 : i ≠ 1 := by
      intro hi
      have := congrArg Fin.val hi
      dsimp [i] at this
      omega
    have heiu : e i ≠ u := by rw [← he0]; exact e.injective.ne hi0
    have heiv : e i ≠ v := by rw [← he1]; exact e.injective.ne hi1
    have hprojection := congrArg K16CoarseKey.secondIsZero? (hkey i)
    have hcanonical := k16CanonicalCoarseKey_second_zero
      n0 n1 n2 start length selected hn0 hn1 hn2 hblock
      position hposition i.isLt
    rw [hcanonical] at hprojection
    constructor
    · intro hs
      simpa [c', i, he1, k16ActualCoarseKey, heiu, heiv,
        K16CoarseKey.secondIsZero?, hs] using hprojection
    · intro hs
      simpa [c', i, he1, k16ActualCoarseKey, heiu, heiv,
        K16CoarseKey.secondIsZero?, hs] using hprojection
  have hzero0 := zeroPrefix 2 5 n0 (Or.inl rfl) (by omega)
  have hzero1 := zeroPrefix 7 4 n1 (Or.inr (Or.inl rfl)) (by omega)
  have hzero2raw := zeroPrefix 11 5 n2 (Or.inr (Or.inr rfl)) (by omega)
  have hzero2 : (coloringValuation c').satisfies_fmla
      (selectRootPrefix 1 11 5 (5 - n0 - n1) 0) := by
    simpa [hn2eq] using hzero2raw
  refine ⟨c', ?_⟩
  change (coloringValuation c').satisfies_fmla (k16BadCommonLeaf n0 n1)
  unfold k16BadCommonLeaf
  have h01 := satisfies_fmla_append hbase hedgeUnit
  have h02 := satisfies_fmla_append h01 hroot0
  have h03 := satisfies_fmla_append h02 hroot1
  have h04 := satisfies_fmla_append h03 hroot2
  have h05 := satisfies_fmla_append h04 hzero0
  have h06 := satisfies_fmla_append h05 hzero1
  exact satisfies_fmla_append h06 hzero2

/-! ## Full endpoint-cell normalization for the sole refined leaf -/

inductive K16FullKey where
  | first
  | second
  | cell (fromFirst fromSecond : ThreeColor)
  deriving DecidableEq

def K16FullKey.firstColor? : K16FullKey → Option ThreeColor
  | .cell p _ => some p
  | _ => none

def K16FullKey.secondColor? : K16FullKey → Option ThreeColor
  | .cell _ q => some q
  | _ => none

def K16FullKey.secondIsZero? : K16FullKey → Option Bool
  | .cell _ q => some (q = 0)
  | _ => none

/-- In the hard coarse cube the zero-column cell sizes are `3,2,0`.
The parameters record the colour-one sizes in the three residual rows. -/
def k16CanonicalHardKey (b0 b1 b2 : Nat) (i : Fin 16) : K16FullKey :=
  if i.val = 0 then .first
  else if i.val = 1 then .second
  else if i.val < 5 then .cell 0 0
  else if i.val < 5 + b0 then .cell 0 1
  else if i.val < 7 then .cell 0 2
  else if i.val < 9 then .cell 1 0
  else if i.val < 9 + b1 then .cell 1 1
  else if i.val < 11 then .cell 1 2
  else if i.val < 11 + b2 then .cell 2 1
  else .cell 2 2

def k16HardCellInterval (b0 b1 b2 : Nat)
    (p q : ThreeColor) : Finset (Fin 16) :=
  if p = 0 then
    if q = 0 then fin16Interval 2 5
    else if q = 1 then fin16Interval 5 (5 + b0)
    else fin16Interval (5 + b0) 7
  else if p = 1 then
    if q = 0 then fin16Interval 7 9
    else if q = 1 then fin16Interval 9 (9 + b1)
    else fin16Interval (9 + b1) 11
  else
    if q = 0 then ∅
    else if q = 1 then fin16Interval 11 (11 + b2)
    else fin16Interval (11 + b2) 16

theorem k16CanonicalHardKey_root0_block
    (b0 b1 b2 start length : Nat) (p : ThreeColor)
    (hb0 : b0 ≤ 2) (hb1 : b1 ≤ 2) (_hb2 : b2 ≤ 5)
    (hblock : (start, length, p) = (2, 5, 0) ∨
      (start, length, p) = (7, 4, 1) ∨
      (start, length, p) = (11, 5, 2))
    (position : Nat) (hposition : position < length)
    (hlabel : start + position < 16) :
    (k16CanonicalHardKey b0 b1 b2
      ⟨start + position, hlabel⟩).firstColor? = some p := by
  rcases hblock with h | h | h
  all_goals
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [k16CanonicalHardKey, K16FullKey.firstColor?]
    all_goals split_ifs
    all_goals simp_all
    all_goals omega

theorem k16CanonicalHardKey_second_zero
    (b0 b1 b2 start length selected : Nat)
    (hb0 : b0 ≤ 2) (_hb1 : b1 ≤ 2) (_hb2 : b2 ≤ 5)
    (hblock : (start, length, selected) = (2, 5, 3) ∨
      (start, length, selected) = (7, 4, 2) ∨
      (start, length, selected) = (11, 5, 0))
    (position : Nat) (hposition : position < length)
    (hlabel : start + position < 16) :
    (k16CanonicalHardKey b0 b1 b2
      ⟨start + position, hlabel⟩).secondIsZero? =
      some (decide (position < selected)) := by
  rcases hblock with h | h | h
  all_goals
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [k16CanonicalHardKey, K16FullKey.secondIsZero?]
    all_goals split_ifs
    all_goals simp_all
    all_goals omega

theorem k16CanonicalHardKey_second_residual
    (b0 b1 b2 start length selected : Nat)
    (hb0 : b0 ≤ 2) (hb1 : b1 ≤ 2) (hb2 : b2 ≤ 5)
    (hblock : (start, length, selected) = (5, 2, b0) ∨
      (start, length, selected) = (9, 2, b1) ∨
      (start, length, selected) = (11, 5, b2))
    (position : Nat) (hposition : position < length)
    (hlabel : start + position < 16) :
    (k16CanonicalHardKey b0 b1 b2
      ⟨start + position, hlabel⟩).secondColor? =
      some (if position < selected then (1 : ThreeColor) else 2) := by
  rcases hblock with h | h | h
  all_goals
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [k16CanonicalHardKey, K16FullKey.secondColor?]
    all_goals split_ifs
    all_goals simp_all
    all_goals omega

theorem k16CanonicalHardKey_first_fiber (b0 b1 b2 : Nat) :
    keyFiber (k16CanonicalHardKey b0 b1 b2) .first = {0} := by
  ext i
  simp only [mem_keyFiber, Finset.mem_singleton]
  simp [k16CanonicalHardKey]
  split_ifs <;> simp_all

theorem k16CanonicalHardKey_second_fiber (b0 b1 b2 : Nat) :
    keyFiber (k16CanonicalHardKey b0 b1 b2) .second = {1} := by
  ext i
  simp only [mem_keyFiber, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h0 : i.val = 0
    · simp [k16CanonicalHardKey, h0] at h
    by_cases h1 : i.val = 1
    · exact Fin.ext h1
    · simp only [k16CanonicalHardKey, h0, h1, ↓reduceIte] at h
      split_ifs at h
  · intro h
    subst i
    simp [k16CanonicalHardKey]

set_option maxHeartbeats 1000000 in
theorem k16CanonicalHardKey_cell_fiber (b0 b1 b2 : Nat)
    (hb0 : b0 ≤ 2) (hb1 : b1 ≤ 2) (hb2 : b2 ≤ 5)
    (p q : ThreeColor) :
    keyFiber (k16CanonicalHardKey b0 b1 b2) (.cell p q) =
      k16HardCellInterval b0 b1 b2 p q := by
  fin_cases p <;> fin_cases q <;> ext i <;>
    simp only [mem_keyFiber] <;>
    simp [k16CanonicalHardKey, k16HardCellInterval] <;>
    split_ifs <;> simp_all <;> omega

def k16ActualFullKey (d : EdgeColoring (Fin 16) ThreeColor)
    (u v x : Fin 16) : K16FullKey :=
  if x = u then .first
  else if x = v then .second
  else .cell (d u x) (d v x)

theorem k16ActualFullKey_first_fiber
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16) (huv : u ≠ v) :
    keyFiber (k16ActualFullKey d u v) .first = {u} := by
  ext x
  simp only [mem_keyFiber, Finset.mem_singleton]
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    simp [k16ActualFullKey, hxu, hxv, huv] at *

theorem k16ActualFullKey_second_fiber
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16) (huv : u ≠ v) :
    keyFiber (k16ActualFullKey d u v) .second = {v} := by
  ext x
  simp only [mem_keyFiber, Finset.mem_singleton]
  by_cases hxu : x = u
  · subst x
    simp [k16ActualFullKey, huv]
  · simp [k16ActualFullKey, hxu]

theorem k16ActualFullKey_cell_fiber
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (p q : ThreeColor) :
    keyFiber (k16ActualFullKey d u v) (.cell p q) =
      k16EndpointCell d u v p q := by
  ext x
  simp only [mem_keyFiber]
  by_cases hxu : x = u
  · subst x
    simp [k16ActualFullKey, k16EndpointCell, k16AwayFrom]
  by_cases hxv : x = v
  · subst x
    simp [k16ActualFullKey, k16EndpointCell, k16AwayFrom, hxu]
  · simp [k16ActualFullKey, k16EndpointCell, k16AwayFrom,
      hxu, hxv]

theorem k16EndpointRow_card_eq_sum_cells
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (p : ThreeColor) :
    (k16EndpointRow d u v p).card =
      (k16EndpointCell d u v p 0).card +
      ((k16EndpointCell d u v p 1).card +
        (k16EndpointCell d u v p 2).card) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := k16EndpointRow d u v p) (t := Finset.univ)
    (f := fun x => d v x) (by simp)
  simpa [Fin.sum_univ_succ, k16EndpointRow, k16EndpointCell,
    Finset.filter_filter, and_assoc, and_left_comm, and_comm] using h

theorem k16EndpointColumn_one_card
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (huv : u ≠ v)
    (hedge : d u v = 1) :
    (k16EndpointColumn d u v 1).card = 4 := by
  rw [k16EndpointColumn_eq_erase_neighborhood]
  have hmem : u ∈ colorNeighborhood d 1 v := by
    simp [huv, d.color_symm, hedge]
  rw [Finset.card_erase_of_mem hmem]
  have hdegree := threeColor_degree_eq_five_at_16 d hd (1 : ThreeColor) v
  change (colorNeighborhood d 1 v).card = 5 at hdegree
  omega

/-- Full cellwise relabeling in the only coarse case not discharged by a
small leaf. -/
theorem exists_k16HardRelabel
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (huv : u ≠ v)
    (hedge : d u v = 1)
    (h00 : (k16EndpointCell d u v 0 0).card = 3)
    (h10 : (k16EndpointCell d u v 1 0).card = 2) :
    let b0 := (k16EndpointCell d u v 0 1).card
    let b1 := (k16EndpointCell d u v 1 1).card
    let b2 := (k16EndpointCell d u v 2 1).card
    ∃ e : Fin 16 ≃ Fin 16,
      e 0 = u ∧ e 1 = v ∧
      ∀ i, k16ActualFullKey d u v (e i) =
        k16CanonicalHardKey b0 b1 b2 i := by
  dsimp only
  let b0 := (k16EndpointCell d u v 0 1).card
  let b1 := (k16EndpointCell d u v 1 1).card
  let b2 := (k16EndpointCell d u v 2 1).card
  have hrow0 : (k16EndpointRow d u v (0 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (0 : ThreeColor)
  have hrow1 : (k16EndpointRow d u v (1 : ThreeColor)).card = 4 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (1 : ThreeColor)
  have hrow2 : (k16EndpointRow d u v (2 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (2 : ThreeColor)
  have hrowsum0 := k16EndpointRow_card_eq_sum_cells d u v (0 : ThreeColor)
  have hrowsum1 := k16EndpointRow_card_eq_sum_cells d u v (1 : ThreeColor)
  have hrowsum2 := k16EndpointRow_card_eq_sum_cells d u v (2 : ThreeColor)
  have hcolsum0 := k16EndpointColumn_card_eq_sum_cells d u v (0 : ThreeColor)
  have hcolcard0 := k16EndpointColumn_zero_card d hd u v huv hedge
  have h20 : (k16EndpointCell d u v 2 0).card = 0 := by omega
  have hb0 : b0 ≤ 2 := by dsimp [b0]; omega
  have hb1 : b1 ≤ 2 := by dsimp [b1]; omega
  have hb2 : b2 ≤ 5 := by dsimp [b2]; omega
  have hcolsum1 := k16EndpointColumn_card_eq_sum_cells d u v (1 : ThreeColor)
  have hcolcard1 := k16EndpointColumn_one_card d hd u v huv hedge
  have hbsum : b0 + (b1 + b2) = 4 := by
    dsimp [b0, b1, b2]
    omega
  have hfibers : ∀ key,
      Fintype.card {i // k16CanonicalHardKey b0 b1 b2 i = key} =
        Fintype.card {x // k16ActualFullKey d u v x = key} := by
    intro key
    rw [card_keyFiber, card_keyFiber]
    cases key with
    | first =>
        rw [k16CanonicalHardKey_first_fiber,
          k16ActualFullKey_first_fiber d u v huv]
        simp
    | second =>
        rw [k16CanonicalHardKey_second_fiber,
          k16ActualFullKey_second_fiber d u v huv]
        simp
    | cell p q =>
        rw [k16CanonicalHardKey_cell_fiber b0 b1 b2 hb0 hb1 hb2,
          k16ActualFullKey_cell_fiber]
        fin_cases p <;> fin_cases q
        · change (fin16Interval 2 5).card =
            (k16EndpointCell d u v 0 0).card
          rw [card_fin16Interval 2 5 (by omega) (by omega)]
          omega
        · change (fin16Interval 5 (5 + b0)).card =
            (k16EndpointCell d u v 0 1).card
          rw [card_fin16Interval 5 (5 + b0) (by omega) (by omega)]
          simp [b0]
        · change (fin16Interval (5 + b0) 7).card =
            (k16EndpointCell d u v 0 2).card
          rw [card_fin16Interval (5 + b0) 7 (by omega) (by omega)]
          dsimp [b0] at *
          omega
        · change (fin16Interval 7 9).card =
            (k16EndpointCell d u v 1 0).card
          rw [card_fin16Interval 7 9 (by omega) (by omega)]
          omega
        · change (fin16Interval 9 (9 + b1)).card =
            (k16EndpointCell d u v 1 1).card
          rw [card_fin16Interval 9 (9 + b1) (by omega) (by omega)]
          simp [b1]
        · change (fin16Interval (9 + b1) 11).card =
            (k16EndpointCell d u v 1 2).card
          rw [card_fin16Interval (9 + b1) 11 (by omega) (by omega)]
          dsimp [b1] at *
          omega
        · change (∅ : Finset (Fin 16)).card =
            (k16EndpointCell d u v 2 0).card
          simp [h20]
        · change (fin16Interval 11 (11 + b2)).card =
            (k16EndpointCell d u v 2 1).card
          rw [card_fin16Interval 11 (11 + b2) (by omega) (by omega)]
          simp [b2]
        · change (fin16Interval (11 + b2) 16).card =
            (k16EndpointCell d u v 2 2).card
          rw [card_fin16Interval (11 + b2) 16 (by omega) (by omega)]
          dsimp [b2] at *
          omega
  let e := equivOfFiberCardEq
    (k16CanonicalHardKey b0 b1 b2) (k16ActualFullKey d u v) hfibers
  refine ⟨e, ?_, ?_, ?_⟩
  · have hkey := equivOfFiberCardEq_map
      (k16CanonicalHardKey b0 b1 b2) (k16ActualFullKey d u v)
      hfibers (0 : Fin 16)
    have hactual : k16ActualFullKey d u v (e 0) = .first := by
      simpa [e, k16CanonicalHardKey] using hkey
    have hmem : e 0 ∈ keyFiber (k16ActualFullKey d u v) .first :=
      (mem_keyFiber _ _ _).2 hactual
    rw [k16ActualFullKey_first_fiber d u v huv] at hmem
    simpa using hmem
  · have hkey := equivOfFiberCardEq_map
      (k16CanonicalHardKey b0 b1 b2) (k16ActualFullKey d u v)
      hfibers (1 : Fin 16)
    have hactual : k16ActualFullKey d u v (e 1) = .second := by
      simpa [e, k16CanonicalHardKey] using hkey
    have hmem : e 1 ∈ keyFiber (k16ActualFullKey d u v) .second :=
      (mem_keyFiber _ _ _).2 hactual
    rw [k16ActualFullKey_second_fiber d u v huv] at hmem
    simpa using hmem
  · intro i
    simpa [e, b0, b1, b2] using
      (equivOfFiberCardEq_map
        (k16CanonicalHardKey b0 b1 b2) (k16ActualFullKey d u v)
        hfibers i)

theorem exists_coloring_satisfying_k16BadCommonHardRefined
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (huv : u ≠ v)
    (hedge : d u v = 1)
    (h00 : (k16EndpointCell d u v 0 0).card = 3)
    (h10 : (k16EndpointCell d u v 1 0).card = 2) :
    ∃ c' : EdgeColoring (Fin 16) ThreeColor,
      (coloringValuation c').satisfies_fmla
        (k16BadCommonHardRefined
          (k16EndpointCell d u v 0 1).card
          (k16EndpointCell d u v 1 1).card) := by
  let b0 := (k16EndpointCell d u v 0 1).card
  let b1 := (k16EndpointCell d u v 1 1).card
  let b2 := (k16EndpointCell d u v 2 1).card
  have hrow0 : (k16EndpointRow d u v (0 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (0 : ThreeColor)
  have hrow1 : (k16EndpointRow d u v (1 : ThreeColor)).card = 4 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (1 : ThreeColor)
  have hrow2 : (k16EndpointRow d u v (2 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (2 : ThreeColor)
  have hrowsum0 := k16EndpointRow_card_eq_sum_cells d u v (0 : ThreeColor)
  have hrowsum1 := k16EndpointRow_card_eq_sum_cells d u v (1 : ThreeColor)
  have hrowsum2 := k16EndpointRow_card_eq_sum_cells d u v (2 : ThreeColor)
  have hcolsum0 := k16EndpointColumn_card_eq_sum_cells d u v (0 : ThreeColor)
  have hcolcard0 := k16EndpointColumn_zero_card d hd u v huv hedge
  have h20 : (k16EndpointCell d u v 2 0).card = 0 := by omega
  have hb0 : b0 ≤ 2 := by dsimp [b0]; omega
  have hb1 : b1 ≤ 2 := by dsimp [b1]; omega
  have hb2 : b2 ≤ 5 := by dsimp [b2]; omega
  have hcolsum1 := k16EndpointColumn_card_eq_sum_cells d u v (1 : ThreeColor)
  have hcolcard1 := k16EndpointColumn_one_card d hd u v huv hedge
  have hbsum : b0 + (b1 + b2) = 4 := by
    dsimp [b0, b1, b2]
    omega
  have hb2eq : 4 - b0 - b1 = b2 := by omega
  rcases exists_k16HardRelabel d hd u v huv hedge h00 h10 with
    ⟨e, he0, he1, hkey⟩
  let c' := relabelVertices d e
  have hgood : NoMonochromaticTriangle c' :=
    noMono_relabelVertices d e hd
  have hbase : (coloringValuation c').satisfies_fmla k16BaseLiteral :=
    coloring_satisfies_k16BaseLiteral c' hgood
  have hedgeUnit : (coloringValuation c').satisfies_fmla (setEdge 0 1 1) := by
    apply coloring_satisfies_setEdge c' (by omega) (by omega) (by omega)
    simpa [c', he0, he1] using hedge
  have rootBlock (start length : Nat) (p : ThreeColor)
      (hblock : (start, length, p) = (2, 5, 0) ∨
        (start, length, p) = (7, 4, 1) ∨
        (start, length, p) = (11, 5, 2))
      (hbound : start + length ≤ 16) :
      (coloringValuation c').satisfies_fmla
        (setRootBlock 0 start length p.val) := by
    apply coloring_satisfies_setRootBlock16 c' 0 start length p.val
      (by omega) hbound p.isLt
    intro position hposition
    let i : Fin 16 := ⟨start + position, by omega⟩
    have hstart : 2 ≤ start := by
      rcases hblock with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        rcases h with ⟨rfl, rfl, rfl⟩ <;> omega
    have hi0 : i ≠ 0 := by
      intro hi; have := congrArg Fin.val hi; dsimp [i] at this; omega
    have hi1 : i ≠ 1 := by
      intro hi; have := congrArg Fin.val hi; dsimp [i] at this; omega
    have heiu : e i ≠ u := by rw [← he0]; exact e.injective.ne hi0
    have heiv : e i ≠ v := by rw [← he1]; exact e.injective.ne hi1
    have hprojection := congrArg K16FullKey.firstColor? (hkey i)
    have hcanonical := k16CanonicalHardKey_root0_block
      b0 b1 b2 start length p hb0 hb1 hb2 hblock position hposition i.isLt
    rw [hcanonical] at hprojection
    simpa [c', i, he0, k16ActualFullKey, heiu, heiv,
      K16FullKey.firstColor?] using hprojection
  have hroot0 := rootBlock 2 5 (0 : ThreeColor) (Or.inl rfl) (by omega)
  have hroot1 := rootBlock 7 4 (1 : ThreeColor) (Or.inr (Or.inl rfl)) (by omega)
  have hroot2 := rootBlock 11 5 (2 : ThreeColor) (Or.inr (Or.inr rfl)) (by omega)
  have zeroPrefix (start length selected : Nat)
      (hblock : (start, length, selected) = (2, 5, 3) ∨
        (start, length, selected) = (7, 4, 2) ∨
        (start, length, selected) = (11, 5, 0))
      (hbound : start + length ≤ 16) :
      (coloringValuation c').satisfies_fmla
        (selectRootPrefix 1 start length selected 0) := by
    apply coloring_satisfies_selectRootPrefix16 c' 1 start length selected 0
      (by omega) hbound (by omega)
    intro position hposition
    let i : Fin 16 := ⟨start + position, by omega⟩
    have hstart : 2 ≤ start := by
      rcases hblock with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        rcases h with ⟨rfl, rfl, rfl⟩ <;> omega
    have hi0 : i ≠ 0 := by
      intro hi; have := congrArg Fin.val hi; dsimp [i] at this; omega
    have hi1 : i ≠ 1 := by
      intro hi; have := congrArg Fin.val hi; dsimp [i] at this; omega
    have heiu : e i ≠ u := by rw [← he0]; exact e.injective.ne hi0
    have heiv : e i ≠ v := by rw [← he1]; exact e.injective.ne hi1
    have hprojection := congrArg K16FullKey.secondIsZero? (hkey i)
    have hcanonical := k16CanonicalHardKey_second_zero
      b0 b1 b2 start length selected hb0 hb1 hb2 hblock
      position hposition i.isLt
    rw [hcanonical] at hprojection
    constructor
    · intro hs
      simpa [c', i, he1, k16ActualFullKey, heiu, heiv,
        K16FullKey.secondIsZero?, hs] using hprojection
    · intro hs
      simpa [c', i, he1, k16ActualFullKey, heiu, heiv,
        K16FullKey.secondIsZero?, hs] using hprojection
  have hzero0 := zeroPrefix 2 5 3 (Or.inl rfl) (by omega)
  have hzero1 := zeroPrefix 7 4 2 (Or.inr (Or.inl rfl)) (by omega)
  have hzero2 := zeroPrefix 11 5 0 (Or.inr (Or.inr rfl)) (by omega)
  have hcoarse : (coloringValuation c').satisfies_fmla
      (k16BadCommonLeaf 3 2) := by
    unfold k16BadCommonLeaf
    have h01 := satisfies_fmla_append hbase hedgeUnit
    have h02 := satisfies_fmla_append h01 hroot0
    have h03 := satisfies_fmla_append h02 hroot1
    have h04 := satisfies_fmla_append h03 hroot2
    have h05 := satisfies_fmla_append h04 hzero0
    have h06 := satisfies_fmla_append h05 hzero1
    simpa using satisfies_fmla_append h06 hzero2
  have residualPrefix (start length selected : Nat)
      (hblock : (start, length, selected) = (5, 2, b0) ∨
        (start, length, selected) = (9, 2, b1) ∨
        (start, length, selected) = (11, 5, b2))
      (hbound : start + length ≤ 16) :
      (coloringValuation c').satisfies_fmla
        (colorRootPrefix 1 start length selected 1 2) := by
    apply coloring_satisfies_colorRootPrefix16 c' 1 start length selected 1 2
      (by omega) hbound (by omega) (by omega)
    intro position hposition
    let i : Fin 16 := ⟨start + position, by omega⟩
    have hstart : 2 ≤ start := by
      rcases hblock with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        rcases h with ⟨rfl, rfl, rfl⟩ <;> omega
    have hi0 : i ≠ 0 := by
      intro hi; have := congrArg Fin.val hi; dsimp [i] at this; omega
    have hi1 : i ≠ 1 := by
      intro hi; have := congrArg Fin.val hi; dsimp [i] at this; omega
    have heiu : e i ≠ u := by rw [← he0]; exact e.injective.ne hi0
    have heiv : e i ≠ v := by rw [← he1]; exact e.injective.ne hi1
    have hprojection := congrArg K16FullKey.secondColor? (hkey i)
    have hcanonical := k16CanonicalHardKey_second_residual
      b0 b1 b2 start length selected hb0 hb1 hb2 hblock
      position hposition i.isLt
    rw [hcanonical] at hprojection
    simpa [c', i, he1, k16ActualFullKey, heiu, heiv,
      K16FullKey.secondColor?] using hprojection
  have hres0 := residualPrefix 5 2 b0 (Or.inl rfl) (by omega)
  have hres1 := residualPrefix 9 2 b1 (Or.inr (Or.inl rfl)) (by omega)
  have hres2raw := residualPrefix 11 5 b2 (Or.inr (Or.inr rfl)) (by omega)
  have hres2 : (coloringValuation c').satisfies_fmla
      (colorRootPrefix 1 11 5 (4 - b0 - b1) 1 2) := by
    simpa [hb2eq] using hres2raw
  refine ⟨c', ?_⟩
  change (coloringValuation c').satisfies_fmla
    (k16BadCommonHardRefined b0 b1)
  unfold k16BadCommonHardRefined
  have h01 := satisfies_fmla_append hcoarse hres0
  have h02 := satisfies_fmla_append h01 hres1
  exact satisfies_fmla_append h02 hres2

/-! ## Discharge of every normalized parameter cube -/

theorem k16_color_one_pair_common_zero_eq_two
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d) (u v : Fin 16) (huv : u ≠ v)
    (hedge : d u v = 1) :
    (k16EndpointCell d u v 0 0).card = 2 := by
  let n0 := (k16EndpointCell d u v 0 0).card
  let n1 := (k16EndpointCell d u v 1 0).card
  let n2 := (k16EndpointCell d u v 2 0).card
  have hrow0 : (k16EndpointRow d u v (0 : ThreeColor)).card = 5 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (0 : ThreeColor)
  have hrow1 : (k16EndpointRow d u v (1 : ThreeColor)).card = 4 := by
    simpa using k16EndpointRow_card d hd u v huv hedge (1 : ThreeColor)
  have hpart0 := k16EndpointCell_zero_add_nonzero d u v (0 : ThreeColor)
  have hpart1 := k16EndpointCell_zero_add_nonzero d u v (1 : ThreeColor)
  have hn0 : n0 ≤ 5 := by dsimp [n0]; omega
  have hn1 : n1 ≤ 4 := by dsimp [n1]; omega
  have hcolsum := k16EndpointColumn_card_eq_sum_cells d u v (0 : ThreeColor)
  have hcolcard := k16EndpointColumn_zero_card d hd u v huv hedge
  have hsum : n0 + (n1 + n2) = 5 := by
    dsimp [n0, n1, n2]
    omega
  by_contra hne
  have hn0ne : n0 ≠ 2 := by simpa [n0] using hne
  rcases exists_coloring_satisfying_k16BadCommonLeaf d hd u v huv hedge with
    ⟨c', hleaf⟩
  change (coloringValuation c').satisfies_fmla (k16BadCommonLeaf n0 n1) at hleaf
  have contradictCoarse {a b : Nat} (ha : n0 = a) (hb : n1 = b)
      (hunsat : (k16BadCommonLeaf a b).proof Sat.Clause.nil) : False := by
    have hs : (coloringValuation c').satisfies_fmla (k16BadCommonLeaf a b) := by
      simpa [ha, hb] using hleaf
    exact hunsat (coloringValuation c') hs
  have hn0cases : n0 = 0 ∨ n0 = 1 ∨ n0 = 2 ∨ n0 = 3 ∨ n0 = 4 ∨ n0 = 5 := by
    omega
  rcases hn0cases with h0 | h0 | h0 | h0 | h0 | h0
  · have h1cases : n1 = 0 ∨ n1 = 1 ∨ n1 = 2 ∨ n1 = 3 ∨ n1 = 4 := by omega
    rcases h1cases with h1 | h1 | h1 | h1 | h1
    · exact contradictCoarse h0 h1 k16_common_0_split_0_unsat
    · exact contradictCoarse h0 h1 k16_common_0_split_1_unsat
    · exact contradictCoarse h0 h1 k16_common_0_split_2_unsat
    · exact contradictCoarse h0 h1 k16_common_0_split_3_unsat
    · exact contradictCoarse h0 h1 k16_common_0_split_4_unsat
  · have h1cases : n1 = 0 ∨ n1 = 1 ∨ n1 = 2 ∨ n1 = 3 ∨ n1 = 4 := by omega
    rcases h1cases with h1 | h1 | h1 | h1 | h1
    · exact contradictCoarse h0 h1 k16_common_1_split_0_unsat
    · exact contradictCoarse h0 h1 k16_common_1_split_1_unsat
    · exact contradictCoarse h0 h1 k16_common_1_split_2_unsat
    · exact contradictCoarse h0 h1 k16_common_1_split_3_unsat
    · exact contradictCoarse h0 h1 k16_common_1_split_4_unsat
  · exact (hn0ne h0).elim
  · have h1cases : n1 = 0 ∨ n1 = 1 ∨ n1 = 2 := by omega
    rcases h1cases with h1 | h1 | h1
    · exact contradictCoarse h0 h1 k16_common_3_split_0_unsat
    · exact contradictCoarse h0 h1 k16_common_3_split_1_unsat
    · have h00 : (k16EndpointCell d u v 0 0).card = 3 := by
        simpa [n0] using h0
      have h10 : (k16EndpointCell d u v 1 0).card = 2 := by
        simpa [n1] using h1
      rcases exists_coloring_satisfying_k16BadCommonHardRefined
          d hd u v huv hedge h00 h10 with ⟨c'', hrefined⟩
      let b0 := (k16EndpointCell d u v 0 1).card
      let b1 := (k16EndpointCell d u v 1 1).card
      change (coloringValuation c'').satisfies_fmla
        (k16BadCommonHardRefined b0 b1) at hrefined
      have hrowsum0 := k16EndpointRow_card_eq_sum_cells d u v (0 : ThreeColor)
      have hrowsum1 := k16EndpointRow_card_eq_sum_cells d u v (1 : ThreeColor)
      have hb0 : b0 ≤ 2 := by dsimp [b0]; omega
      have hb1 : b1 ≤ 2 := by dsimp [b1]; omega
      have contradictRefined {a b : Nat} (ha : b0 = a) (hb : b1 = b)
          (hunsat : (k16BadCommonHardRefined a b).proof Sat.Clause.nil) : False := by
        have hs : (coloringValuation c'').satisfies_fmla
            (k16BadCommonHardRefined a b) := by
          simpa [ha, hb] using hrefined
        exact hunsat (coloringValuation c'') hs
      have hb0cases : b0 = 0 ∨ b0 = 1 ∨ b0 = 2 := by omega
      have hb1cases : b1 = 0 ∨ b1 = 1 ∨ b1 = 2 := by omega
      rcases hb0cases with hb0' | hb0' | hb0' <;>
        rcases hb1cases with hb1' | hb1' | hb1'
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_0_0_4_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_0_1_3_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_0_2_2_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_1_0_3_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_1_1_2_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_1_2_1_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_2_0_2_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_2_1_1_unsat
      · exact contradictRefined hb0' hb1'
          k16_common_3_split_2_blue_2_2_0_unsat
  · have h1cases : n1 = 0 ∨ n1 = 1 := by omega
    rcases h1cases with h1 | h1
    · exact contradictCoarse h0 h1 k16_common_4_split_0_unsat
    · exact contradictCoarse h0 h1 k16_common_4_split_1_unsat
  · have h1 : n1 = 0 := by omega
    exact contradictCoarse h0 h1 k16_common_5_split_0_unsat

theorem k16EndpointCell_eq_commonNeighborhoods
    (d : EdgeColoring (Fin 16) ThreeColor) (u v : Fin 16)
    (p q : ThreeColor) :
    k16EndpointCell d u v p q =
      colorNeighborhood d p u ∩ colorNeighborhood d q v := by
  ext x
  simp [k16EndpointCell, k16AwayFrom, colorNeighborhood,
    and_assoc, and_left_comm, and_comm]

/-- Arbitrary-colour form of the checked K16 common-neighbour theorem. -/
theorem k16_noncolor_pair_common_neighbors_eq_two
    (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (q : ThreeColor)
    (u v : Fin 16) (huv : u ≠ v) (hneq : c u v ≠ q) :
    (colorNeighborhood c q u ∩ colorNeighborhood c q v).card = 2 := by
  let s : Equiv.Perm ThreeColor := Equiv.swap q 0
  let e : Equiv.Perm ThreeColor :=
    s.trans (Equiv.swap (s (c u v)) 1)
  have hsq : s q = 0 := by
    exact Equiv.swap_apply_left q 0
  have hsedge : s (c u v) ≠ 0 := by
    intro h
    apply hneq
    apply s.injective
    exact h.trans hsq.symm
  have heq : e q = 0 := by
    rw [Equiv.trans_apply, hsq]
    exact Equiv.swap_apply_of_ne_of_ne hsedge.symm (by decide)
  have heEdge : e (c u v) = 1 := by
    rw [Equiv.trans_apply]
    exact Equiv.swap_apply_left (s (c u v)) 1
  let d := mapEdgeColors c e
  have hd : NoMonochromaticTriangle d := noMono_mapEdgeColors c e hc
  have hdedge : d u v = 1 := by simpa [d] using heEdge
  have hnorm := k16_color_one_pair_common_zero_eq_two d hd u v huv hdedge
  rw [k16EndpointCell_eq_commonNeighborhoods] at hnorm
  have hesymm : e.symm 0 = q := by
    apply e.injective
    simp [heq]
  have hNu : colorNeighborhood d 0 u = colorNeighborhood c q u := by
    rw [colorNeighborhood_mapEdgeColors]
    exact congrArg (fun r => colorNeighborhood c r u) hesymm
  have hNv : colorNeighborhood d 0 v = colorNeighborhood c q v := by
    rw [colorNeighborhood_mapEdgeColors]
    exact congrArg (fun r => colorNeighborhood c r v) hesymm
  rwa [hNu, hNv] at hnorm

theorem colorGraph_neighborFinset_eq_colorNeighborhood
    (c : EdgeColoring (Fin 16) ThreeColor) (q : ThreeColor) (v : Fin 16) :
    (colorGraph c q).neighborFinset v = colorNeighborhood c q v := by
  classical
  ext w
  simp [colorGraph, colorNeighborhood, eq_comm]

theorem colorGraph_commonNeighbors_card_eq
    (c : EdgeColoring (Fin 16) ThreeColor) (q : ThreeColor) (u v : Fin 16) :
    Fintype.card ((colorGraph c q).commonNeighbors u v) =
      (colorNeighborhood c q u ∩ colorNeighborhood c q v).card := by
  classical
  let S : Set (Fin 16) := (colorGraph c q).commonNeighbors u v
  let T : Set (Fin 16) :=
    ↑(colorNeighborhood c q u ∩ colorNeighborhood c q v)
  have hST : S = T := by
    ext x
    simp [S, T, SimpleGraph.commonNeighbors, colorGraph, colorNeighborhood,
      eq_comm, and_assoc, and_left_comm]
  let e : S ≃ T := Equiv.setCongr hST
  calc
    Fintype.card ((colorGraph c q).commonNeighbors u v) =
        Fintype.card S := rfl
    _ = Fintype.card T := Fintype.card_congr e
    _ = (colorNeighborhood c q u ∩ colorNeighborhood c q v).card := by
      exact Fintype.card_coe _

/-- Each colour graph of a good K16 three-colouring is the strongly regular
graph with parameters `(16,5,0,2)`. -/
theorem k16_colorGraph_isSRG
    (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (q : ThreeColor) :
    (colorGraph c q).IsSRGWith 16 5 0 2 := by
  classical
  refine SimpleGraph.IsSRGWith.mk (by rfl) ?_ ?_ ?_
  · intro v
    rw [← (colorGraph c q).card_neighborFinset_eq_degree]
    rw [colorGraph_neighborFinset_eq_colorNeighborhood]
    simpa [colorDegree] using threeColor_degree_eq_five_at_16 c hc q v
  · intro u v hadj
    rw [colorGraph_commonNeighbors_card_eq]
    apply Finset.card_eq_zero.mpr
    ext x
    simp only [Finset.notMem_empty, iff_false, Finset.mem_inter,
      mem_colorNeighborhood]
    rintro ⟨⟨hxu, hux⟩, hxv, hvx⟩
    have huv : u ≠ v := hadj.1
    have huvColor : c u v = q := hadj.2
    apply hc u v x
    · exact ⟨huv, hxu.symm, hxv.symm⟩
    · exact ⟨huvColor.trans hux.symm,
        hux.trans hvx.symm⟩
  · intro u v huv hnotAdj
    rw [colorGraph_commonNeighbors_card_eq]
    have hneq : c u v ≠ q := by
      intro hcolor
      exact hnotAdj ⟨huv, hcolor⟩
    exact k16_noncolor_pair_common_neighbors_eq_two c hc q u v huv hneq

#print axioms R4333.k16_color_one_pair_common_zero_eq_two
#print axioms R4333.k16_noncolor_pair_common_neighbors_eq_two
#print axioms R4333.k16_colorGraph_isSRG

end R4333
