import UniformK60.BalancedEncodingData
import UniformK60.BalancedHostGuard

/-! Soundness of the fixed-edge simplification in each global degree bound. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 Ramsey61.DenseCounter Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.BalancedHost UniformK60.BalancedEncoding UniformK60.HostNormalization

set_option maxRecDepth 100000 in
theorem canonical_rootColor : ∀ v : Vertex, v ≠ 0 →
    canonicalCell false v = some (palette (rootColor v)) := by decide

set_option maxRecDepth 100000 in
theorem x_coordinates : ∀ v : Vertex, inX v = true →
    ∃ i : Fin 15, x i = v ∧ localX v = i.castSucc := by decide

set_option maxRecDepth 100000 in
theorem y_coordinates : ∀ v : Vertex, inY v = true →
    ∃ i : Fin 16, y i = v ∧ localY v = i := by decide

theorem fixedColor_match {c : Host} {o : Owner} (hn : Normalized false c o)
    (a b : Vertex) (hab : a ≠ b) (q : Color) (h : fixedColor o a b = some q) :
    c a b = palette q := by
  unfold fixedColor at h
  split_ifs at h with ha hb hx hy
  · subst a
    have hedge : c 0 b = palette (rootColor b) := by
      have hh := hn.spokes b
      rw [canonical_rootColor b hab.symm] at hh
      exact ((mem_colorNeighborhood _ _ _ _).mp ((rootCell_some c 0 b (Equiv.refl _) _).mp hh)).2
    exact hedge.trans (congrArg palette (Option.some.inj h))
  · subst b
    have hedge : c 0 a = palette (rootColor a) := by
      have hh := hn.spokes a
      rw [canonical_rootColor a ha] at hh
      exact ((mem_colorNeighborhood _ _ _ _).mp ((rootCell_some c 0 a (Equiv.refl _) _).mp hh)).2
    rw [c.color_symm]
    exact hedge.trans (congrArg palette (Option.some.inj h))
  · obtain ⟨hxa,hxb⟩ := Bool.and_eq_true_iff.mp hx
    obtain ⟨i,hi,hic⟩ := x_coordinates a hxa
    obtain ⟨j,hj,hjc⟩ := x_coordinates b hxb
    have hij : i ≠ j := by intro he;exact hab (hi.symm.trans ((congrArg x he).trans hj))
    have hedge := hn.left_template i j hij
    change c (x i) (x j) = _ at hedge
    rw [hi,hj] at hedge
    rw [hic,hjc] at h
    exact hedge.trans (congrArg palette (Option.some.inj h))
  · obtain ⟨hya,hyb⟩ := Bool.and_eq_true_iff.mp hy
    obtain ⟨i,hi,hic⟩ := y_coordinates a hya
    obtain ⟨j,hj,hjc⟩ := y_coordinates b hyb
    have hij : i ≠ j := by intro he;exact hab (hi.symm.trans ((congrArg y he).trans hj))
    have hedge := hn.right_template i j hij
    change c (y i) (y j) = _ at hedge
    rw [hi,hj] at hedge
    rw [hic,hjc] at h
    exact hedge.trans (congrArg palette (Option.some.inj h))

theorem physical_matches (c : Host) : PhysicalMatches (physicalValuation c) c := by
  intro a b hab q
  have h := physicalValuation_edge c a b q hab
  cases hh : physicalValuation c (edgeVar a b q) <;> simp_all

theorem prefixCount_take {α : Type} (xs : List α) (fallback : α) (p : α → Bool)
    (n : Nat) (hn : n ≤ xs.length) :
    SequentialCounter.prefixCount (fun i => p (xs.getD i fallback)) n =
      ((xs.take n).filter p).length := by
  induction n with
  | zero => simp [SequentialCounter.prefixCount]
  | succ n ih =>
    have hlt : n < xs.length := by omega
    rw [SequentialCounter.prefixCount,ih (by omega),List.take_succ_eq_append_getElem hlt]
    rw [List.filter_append,List.length_append]
    rw [←List.getElem_eq_getD (h:=hlt) fallback]
    cases h : p xs[n] <;> simp [h]

theorem prefixCount_list {α : Type} (xs : List α) (fallback : α) (p : α → Bool) :
    SequentialCounter.prefixCount (fun i => p (xs.getD i fallback)) xs.length =
      (xs.filter p).length := by
  simpa only [List.take_length] using prefixCount_take xs fallback p xs.length (le_refl _)

theorem fin_filter_length {n : Nat} (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = (univ.filter fun v => p v).card := by
  have hnodup := (List.nodup_finRange n).filter p
  rw [←List.toFinset_card_of_nodup hnodup,List.toFinset_filter]
  congr
  ext x
  simp

def unknownTrue (c : Host) (o : Owner) (v : Vertex) (q : Color) : Finset Vertex :=
  univ.filter fun u => u ≠ v ∧ fixedColor o v u = none ∧ c v u = palette q

def knownSet (o : Owner) (v : Vertex) (q : Color) : Finset Vertex :=
  univ.filter fun u => u ≠ v ∧ fixedColor o v u = some q

theorem knownTrue_card (o : Owner) (v : Vertex) (q : Color) :
    knownTrue o v q = (knownSet o v q).card := by
  simpa only [knownTrue,knownSet,decide_eq_true_eq] using
    (fin_filter_length (fun u : Vertex => decide (u ≠ v ∧ fixedColor o v u = some q)))

theorem neighbor_partition {c : Host} {o : Owner} (hn : Normalized false c o)
    (v : Vertex) (q : Color) :
    Disjoint (unknownTrue c o v q) (knownSet o v q) ∧
      unknownTrue c o v q ∪ knownSet o v q = colorNeighborhood c (palette q) v := by
  constructor
  · apply disjoint_left.mpr
    intro u hu hk
    simp only [unknownTrue,knownSet,mem_filter,mem_univ,true_and] at hu hk
    rw [hu.2.1] at hk
    cases hk.2
  · ext u
    simp only [mem_union,unknownTrue,knownSet,mem_filter,mem_univ,true_and,mem_colorNeighborhood]
    constructor
    · rintro (⟨hu,_,hc⟩ | ⟨hu,hc⟩)
      · exact ⟨hu,hc⟩
      · exact ⟨hu,fixedColor_match hn v u hu.symm q hc⟩
    · rintro ⟨hu,hc⟩
      cases hf : fixedColor o v u with
      | none => exact Or.inl ⟨hu,rfl,hc⟩
      | some r =>
        have hr := fixedColor_match hn v u hu.symm r hf
        have he : r = q := palette_injective (hr.symm.trans hc)
        exact Or.inr ⟨hu,by simpa only [he] using hf⟩

theorem unknownTrue_bound {c : Host} {o : Owner} (hn : Normalized false c o)
    (v : Vertex) (q : Color) :
    (unknownTrue c o v q).card ≤ degreeBound o v q := by
  obtain ⟨hd,he⟩ := neighbor_partition hn v q
  have hs := card_union_of_disjoint hd
  rw [he] at hs
  change colorDegree c (palette q) v = _ at hs
  have hcap := hn.caps v q
  change colorDegree c (palette q) v ≤ cap q at hcap
  rw [degreeBound,knownTrue_card]
  omega

/-- The reduced list contains each currently unfixed physical edge once. -/
theorem degree_input_bound (o : Owner) (v : Vertex) (q : Color) (i : Nat)
    (hi : i < (unknownNeighbors o v).length) : degreeInput o v q i ≤ 7080 := by
  have hm : (unknownNeighbors o v).getD i 0 ∈ unknownNeighbors o v := by
    rw [←List.getElem_eq_getD 0]
    exact List.getElem_mem hi
  have hne : (unknownNeighbors o v).getD i 0 ≠ v := by
    exact (of_decide_eq_true (List.mem_filter.mp hm).2).1
  have h := (edgeVar_bounds v ((unknownNeighbors o v).getD i 0) q hne.symm).2
  unfold degreeInput
  omega

theorem degree_input_count {c : Host} {o : Owner} (hn : Normalized false c o)
    (v : Vertex) (q : Color) :
    SequentialCounter.prefixCount (fun i => physicalValuation c (degreeInput o v q i))
      (unknownNeighbors o v).length = (unknownTrue c o v q).card := by
  simp only [degreeInput]
  rw [prefixCount_list (unknownNeighbors o v) 0 (fun u : Vertex => physicalValuation c (edgeVar v u q))]
  rw [unknownNeighbors,List.filter_filter]
  have hf : (fun u : Vertex =>
      physicalValuation c (edgeVar v u q) && decide (u ≠ v ∧ fixedColor o v u = none)) =
      (fun u => decide (u ≠ v ∧ fixedColor o v u = none ∧ c v u = palette q)) := by
    funext u
    by_cases hu : u = v
    · simp [hu]
    · rw [physical_matches c v u (Ne.symm hu) q]
      simp [hu,Bool.and_comm]
  rw [hf]
  simpa only [unknownTrue,decide_eq_true_eq] using
    (fin_filter_length (fun u : Vertex => decide (u ≠ v ∧ fixedColor o v u = none ∧ c v u = palette q)))

#print axioms fixedColor_match
#print axioms unknownTrue_bound
#print axioms degree_input_count
end UniformK60.BalancedEncodingData
