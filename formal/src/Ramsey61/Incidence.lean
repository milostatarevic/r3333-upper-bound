import Ramsey61.Profiles
namespace Ramsey61
open Finset

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


end Ramsey61
