import R4333Lean.SingleRootStarReduction61
import R4333Lean.DegreeTargets61

/-!
# A high-own-incidence root at order 61

For an oriented pair `(root, endpoint)`, call the incidence high when the
endpoint has full degree at least fifteen in the colour of the joining edge.
Every vertex having a degree-sixteen colour contributes at least 32 incoming
high incidences; a vertex with no degree-sixteen colour has all four degrees
fifteen and contributes all 60 incidences.

Double counting, together with the capacity 60 at every root, forces a root
which itself has a degree-sixteen colour and receives at least 32 high
incidences.  This is a semantic averaging theorem; no finite search or SAT
assumption occurs here.
-/

namespace R4333
namespace HighOwnIncidenceRootSelection61

open Finset SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

def HasDegreeSixteen {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (v : V) : Prop :=
  ∃ q : FourColor, colorDegree c q v = 16

def highOwnNeighborSupport {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) : Finset V :=
  Finset.univ.filter fun endpoint =>
    endpoint ≠ root ∧ 15 ≤ colorDegree c (c root endpoint) endpoint

def highOwnNeighborCount {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root : V) : Nat :=
  (highOwnNeighborSupport c root).card

def incomingHighOwnSupport {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (endpoint : V) : Finset V :=
  Finset.univ.filter fun root =>
    root ≠ endpoint ∧ 15 ≤ colorDegree c (c root endpoint) endpoint

def criticalDegreeMass {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (v : V) : Nat :=
  ∑ q : FourColor,
    if 15 ≤ colorDegree c q v then colorDegree c q v else 0

@[simp] theorem mem_highOwnNeighborSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (root endpoint : V) :
    endpoint ∈ highOwnNeighborSupport c root ↔
      endpoint ≠ root ∧
        15 ≤ colorDegree c (c root endpoint) endpoint := by
  simp [highOwnNeighborSupport]

theorem total_highOwn_eq_total_incoming
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) :
    (∑ root : V, highOwnNeighborCount c root) =
      ∑ endpoint : V, (incomingHighOwnSupport c endpoint).card := by
  classical
  simp only [highOwnNeighborCount, highOwnNeighborSupport,
    incomingHighOwnSupport, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro endpoint _hendpoint
  apply Finset.sum_congr rfl
  intro root _hroot
  by_cases heq : endpoint = root
  · subst root
    simp
  · have heq' : root ≠ endpoint := Ne.symm heq
    simp [heq, heq']

theorem incomingHighOwnSupport_card_eq_criticalDegreeMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (endpoint : V) :
    (incomingHighOwnSupport c endpoint).card =
      criticalDegreeMass c endpoint := by
  classical
  let support : Finset V := Finset.univ.filter fun root =>
    root ≠ endpoint ∧
      15 ≤ colorDegree c (c endpoint root) endpoint
  have hincoming : incomingHighOwnSupport c endpoint = support := by
    ext root
    simp only [incomingHighOwnSupport, support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [c.color_symm root endpoint]
  rw [hincoming]
  have hpartition :
      support.card =
        ∑ q ∈ (Finset.univ : Finset FourColor),
          #{root ∈ support | c endpoint root = q} :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hpartition]
  simp only [criticalDegreeMass]
  apply Finset.sum_congr rfl
  intro q _hqmem
  by_cases hq : 15 ≤ colorDegree c q endpoint
  · simp only [if_pos hq]
    rw [colorDegree]
    congr 1
    ext root
    simp only [support, Finset.mem_filter, Finset.mem_univ,
      true_and, mem_colorNeighborhood]
    constructor
    · rintro ⟨⟨hne, _hcritical⟩, hcolor⟩
      exact ⟨hne, hcolor⟩
    · rintro ⟨hne, hcolor⟩
      exact ⟨⟨hne, by simpa [hcolor] using hq⟩, hcolor⟩
  · simp only [if_neg hq]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro root hroot hcolor
    simp only [support, Finset.mem_filter, Finset.mem_univ,
      true_and] at hroot
    exact hq (by simpa [hcolor] using hroot.2)

theorem total_highOwn_eq_total_criticalDegreeMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) :
    (∑ root : V, highOwnNeighborCount c root) =
      ∑ endpoint : V, criticalDegreeMass c endpoint := by
  rw [total_highOwn_eq_total_incoming]
  apply Finset.sum_congr rfl
  intro endpoint _
  exact incomingHighOwnSupport_card_eq_criticalDegreeMass c endpoint

/-! ## Local contribution bounds -/

theorem criticalDegreeMass_arithmetic_ge_thirtyTwo
    (a b d e : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hd : d ≤ 16) (he : e ≤ 16)
    (hsum : a + b + d + e = 60)
    (_hsixteen : a = 16 ∨ b = 16 ∨ d = 16 ∨ e = 16) :
    32 ≤ (if 15 ≤ a then a else 0) +
      (if 15 ≤ b then b else 0) +
      (if 15 ≤ d then d else 0) +
      (if 15 ≤ e then e else 0) := by
  split_ifs <;> omega

theorem all_degrees_fifteen_of_not_hasDegreeSixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (v : V) (hnot : ¬HasDegreeSixteen c v) :
    ∀ q : FourColor, colorDegree c q v = 15 := by
  have h00 := fourColor_colorDegree_le_sixteen c hc (false, false) v
  have h01 := fourColor_colorDegree_le_sixteen c hc (false, true) v
  have h10 := fourColor_colorDegree_le_sixteen c hc (true, false) v
  have h11 := fourColor_colorDegree_le_sixteen c hc (true, true) v
  have hn00 : colorDegree c (false, false) v ≠ 16 := by
    intro h
    exact hnot ⟨(false, false), h⟩
  have hn01 : colorDegree c (false, true) v ≠ 16 := by
    intro h
    exact hnot ⟨(false, true), h⟩
  have hn10 : colorDegree c (true, false) v ≠ 16 := by
    intro h
    exact hnot ⟨(true, false), h⟩
  have hn11 : colorDegree c (true, true) v ≠ 16 := by
    intro h
    exact hnot ⟨(true, true), h⟩
  have hsum := fourColor_degree_sum c v
  rw [hcard] at hsum
  intro q
  fin_cases q <;> simp_all <;> omega

theorem criticalDegreeMass_eq_sixty_of_not_hasDegreeSixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (v : V) (hnot : ¬HasDegreeSixteen c v) :
    criticalDegreeMass c v = 60 := by
  have hall := all_degrees_fifteen_of_not_hasDegreeSixteen
    hcard c hc v hnot
  simp [criticalDegreeMass, hall]

theorem criticalDegreeMass_ge_thirtyTwo_of_hasDegreeSixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (v : V) (hsixteen : HasDegreeSixteen c v) :
    32 ≤ criticalDegreeMass c v := by
  have h00 := fourColor_colorDegree_le_sixteen c hc (false, false) v
  have h01 := fourColor_colorDegree_le_sixteen c hc (false, true) v
  have h10 := fourColor_colorDegree_le_sixteen c hc (true, false) v
  have h11 := fourColor_colorDegree_le_sixteen c hc (true, true) v
  have hsum := fourColor_degree_sum c v
  rw [hcard] at hsum
  obtain ⟨q, hq⟩ := hsixteen
  have hsixteen' :
      colorDegree c (false, false) v = 16 ∨
      colorDegree c (false, true) v = 16 ∨
      colorDegree c (true, false) v = 16 ∨
      colorDegree c (true, true) v = 16 := by
    fin_cases q <;> simp_all
  have harithmetic := criticalDegreeMass_arithmetic_ge_thirtyTwo
    (colorDegree c (false, false) v)
    (colorDegree c (false, true) v)
    (colorDegree c (true, false) v)
    (colorDegree c (true, true) v)
    h00 h01 h10 h11 (by omega) hsixteen'
  simpa [criticalDegreeMass, FourColor, Fintype.sum_prod_type,
    Fintype.sum_bool, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using harithmetic

theorem highOwnNeighborCount_le_sixty
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (root : V) :
    highOwnNeighborCount c root ≤ 60 := by
  have hsubset : highOwnNeighborSupport c root ⊆
      (Finset.univ : Finset V).erase root := by
    intro endpoint hendpoint
    have hne := (mem_highOwnNeighborSupport c root endpoint).mp hendpoint |>.1
    simp [hne]
  calc
    highOwnNeighborCount c root = (highOwnNeighborSupport c root).card := rfl
    _ ≤ ((Finset.univ : Finset V).erase root).card :=
      Finset.card_le_card hsubset
    _ = 60 := by simp [hcard]

/-! ## Global root selection -/

noncomputable def degreeSixteenVertices {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) : Finset V := by
  classical
  exact Finset.univ.filter (HasDegreeSixteen c)

@[simp] theorem mem_degreeSixteenVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (v : V) :
    v ∈ degreeSixteenVertices c ↔ HasDegreeSixteen c v := by
  simp [degreeSixteenVertices]

/-- A good four-colouring on 61 vertices has a degree-sixteen root receiving
at least 32 high own-colour incidences. -/
theorem exists_degreeSixteen_root_highOwn_ge_thirtyTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    ∃ root : V, HasDegreeSixteen c root ∧
      32 ≤ highOwnNeighborCount c root := by
  classical
  by_contra hnone
  let S : Finset V := degreeSixteenVertices c
  obtain ⟨rootSixteen, qSixteen, hrootSixteen⟩ :=
    exists_colorDegree_eq_sixteen_at_61 hcard c hc
  have hrootMem : rootSixteen ∈ S := by
    change rootSixteen ∈ degreeSixteenVertices c
    rw [mem_degreeSixteenVertices]
    exact ⟨qSixteen, hrootSixteen⟩
  have hSpositive : 1 ≤ S.card := Finset.one_le_card.mpr ⟨rootSixteen, hrootMem⟩
  have hlowerPoint (v : V) :
      (if HasDegreeSixteen c v then 32 else 60) ≤
        criticalDegreeMass c v := by
    by_cases hv : HasDegreeSixteen c v
    · simpa [hv] using
        criticalDegreeMass_ge_thirtyTwo_of_hasDegreeSixteen hcard c hc v hv
    · have heq := criticalDegreeMass_eq_sixty_of_not_hasDegreeSixteen
        hcard c hc v hv
      simp [hv, heq]
  have hupperPoint (v : V) :
      highOwnNeighborCount c v ≤
        if HasDegreeSixteen c v then 31 else 60 := by
    by_cases hv : HasDegreeSixteen c v
    · have hnot : ¬32 ≤ highOwnNeighborCount c v := by
        intro hhigh
        exact hnone ⟨v, hv, hhigh⟩
      simp [hv]
      omega
    · simpa [hv] using highOwnNeighborCount_le_sixty hcard c v
  have hlowerSum :
      (∑ v : V, if HasDegreeSixteen c v then 32 else 60) ≤
        ∑ v : V, criticalDegreeMass c v :=
    Finset.sum_le_sum fun v _ => hlowerPoint v
  have hupperSum :
      (∑ v : V, highOwnNeighborCount c v) ≤
        ∑ v : V, if HasDegreeSixteen c v then 31 else 60 :=
    Finset.sum_le_sum fun v _ => hupperPoint v
  have hgap :
      (∑ v : V, if HasDegreeSixteen c v then 32 else 60) =
        (∑ v : V, if HasDegreeSixteen c v then 31 else 60) + S.card := by
    calc
      (∑ v : V, if HasDegreeSixteen c v then 32 else 60) =
          ∑ v : V, ((if HasDegreeSixteen c v then 31 else 60) +
            if HasDegreeSixteen c v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v _hv
        by_cases hsixteen : HasDegreeSixteen c v <;> simp [hsixteen]
      _ = (∑ v : V, if HasDegreeSixteen c v then 31 else 60) +
          ∑ v : V, if HasDegreeSixteen c v then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ v : V, if HasDegreeSixteen c v then 31 else 60) + S.card := by
        congr 1
        simp only [S, degreeSixteenVertices, Finset.card_filter]
  have htotal := total_highOwn_eq_total_criticalDegreeMass c
  have himpossible :
      (∑ v : V, if HasDegreeSixteen c v then 31 else 60) + S.card ≤
        ∑ v : V, if HasDegreeSixteen c v then 31 else 60 := by
    calc
      (∑ v : V, if HasDegreeSixteen c v then 31 else 60) + S.card =
          ∑ v : V, if HasDegreeSixteen c v then 32 else 60 := hgap.symm
      _ ≤ ∑ v : V, criticalDegreeMass c v := hlowerSum
      _ = ∑ v : V, highOwnNeighborCount c v := htotal.symm
      _ ≤ ∑ v : V, if HasDegreeSixteen c v then 31 else 60 := hupperSum
  omega

#print axioms R4333.HighOwnIncidenceRootSelection61.total_highOwn_eq_total_criticalDegreeMass
#print axioms R4333.HighOwnIncidenceRootSelection61.criticalDegreeMass_ge_thirtyTwo_of_hasDegreeSixteen
#print axioms R4333.HighOwnIncidenceRootSelection61.exists_degreeSixteen_root_highOwn_ge_thirtyTwo

end HighOwnIncidenceRootSelection61
end R4333
