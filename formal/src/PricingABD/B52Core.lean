import PricingABD.BPhysicalBounds

namespace PricingABD.B52Core
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
abbrev Vertex := Fin 52
abbrev Color := Fin 4
abbrev Coloring := EdgeColoring Vertex FourColor

/-- Start of the lexicographic unordered-edge row, exactly `u*(103-u)//2`. -/
def rowStart (u : Nat) : Nat := u * (103 - u) / 2

/- A small finite arithmetic table (52 by 52), not an assumed edge map. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem rowStart_separated : ∀ u v : Vertex, u < v →
    rowStart u.val + (51 - u.val) ≤ rowStart v.val := by decide

set_option maxRecDepth 10000 in
theorem rowStart_bounded : ∀ u : Vertex,
    rowStart u.val + (51 - u.val) ≤ 1326 := by decide

def edgeRank (u v : Vertex) : Nat := rowStart u.val + (v.val - u.val - 1)

def orderedEdgeVar (u v : Vertex) (q : Color) : Nat :=
  4 * edgeRank u v + q.val + 1

/-- Unordered-edge lookup used by degree input lists. -/
def edgeVar (u v : Vertex) (q : Color) : Nat :=
  if u < v then orderedEdgeVar u v q else orderedEdgeVar v u q

theorem edgeRank_bounds (u v : Vertex) (h : u < v) :
    rowStart u.val ≤ edgeRank u v ∧
      edgeRank u v < rowStart u.val + (51 - u.val) := by
  have hv := v.isLt
  change u.val < v.val at h
  unfold edgeRank
  omega

theorem edgeRank_injective (u v x y : Vertex) (huv : u < v) (hxy : x < y)
    (heq : edgeRank u v = edgeRank x y) : u = x ∧ v = y := by
  have hb := edgeRank_bounds u v huv
  have hc := edgeRank_bounds x y hxy
  have hux : u = x := by
    rcases lt_trichotomy u x with h | h | h
    · have hs := rowStart_separated u x h; omega
    · exact h
    · have hs := rowStart_separated x u h; omega
  subst x
  refine ⟨rfl, Fin.ext ?_⟩
  have hv := v.isLt
  have hy := y.isLt
  change u.val < v.val at huv
  change u.val < y.val at hxy
  unfold edgeRank at heq
  omega

theorem orderedEdgeVar_injective (u v x y : Vertex) (q r : Color)
    (huv : u < v) (hxy : x < y)
    (heq : orderedEdgeVar u v q = orderedEdgeVar x y r) :
    u = x ∧ v = y ∧ q = r := by
  have hq := q.isLt
  have hr := r.isLt
  have heq' := heq
  unfold orderedEdgeVar at heq'
  have hrank : edgeRank u v = edgeRank x y := by omega
  obtain ⟨hu,hv⟩ := edgeRank_injective u v x y huv hxy hrank
  refine ⟨hu,hv,Fin.ext ?_⟩
  omega

theorem orderedEdgeVar_bounds (u v : Vertex) (q : Color) (huv : u < v) :
    1 ≤ orderedEdgeVar u v q ∧ orderedEdgeVar u v q < 5305 := by
  have hb := edgeRank_bounds u v huv
  have hs := rowStart_bounded u
  have hq := q.isLt
  unfold orderedEdgeVar
  omega

/-- The left-associated integer expression in Python, on its valid domain. -/
theorem orderedEdgeVar_python_formula (u v : Vertex) (q : Color) (huv : u < v) :
    orderedEdgeVar u v q =
      4 * (u.val * (104 - u.val - 1) / 2 + v.val - u.val - 1) + q.val + 1 := by
  have hu := u.isLt
  change u.val < v.val at huv
  have hsub : 104 - u.val - 1 = 103 - u.val := by omega
  rw [hsub]
  unfold orderedEdgeVar edgeRank rowStart
  omega

theorem edgeVar_bounds (u v : Vertex) (q : Color) (hne : u ≠ v) :
    1 ≤ edgeVar u v q ∧ edgeVar u v q < 5305 := by
  unfold edgeVar
  split_ifs with h
  · exact orderedEdgeVar_bounds u v q h
  · exact orderedEdgeVar_bounds v u q (lt_of_le_of_ne (le_of_not_gt h) hne.symm)

/-- This direct finite interpretation avoids trusting an external inverse map. -/
noncomputable def physicalValuation (c : Coloring) : Valuation := by
  classical
  exact fun atom => decide (∃ u v : Vertex, ∃ q : Color,
    u < v ∧ atom = orderedEdgeVar u v q ∧ c u v = palette q)

theorem physicalValuation_ordered (c : Coloring) (u v : Vertex) (q : Color)
    (huv : u < v) :
    physicalValuation c (orderedEdgeVar u v q) = true ↔ c u v = palette q := by
  classical
  simp only [physicalValuation, decide_eq_true_eq]
  constructor
  · rintro ⟨x,y,r,hxy,heq,hcolor⟩
    obtain ⟨rfl,rfl,rfl⟩ := orderedEdgeVar_injective u v x y q r huv hxy heq
    exact hcolor
  · intro h
    exact ⟨u,v,q,huv,rfl,h⟩

theorem physicalValuation_edge (c : Coloring) (u v : Vertex) (q : Color)
    (hne : u ≠ v) :
    physicalValuation c (edgeVar u v q) = true ↔ c u v = palette q := by
  unfold edgeVar
  split_ifs with h
  · exact physicalValuation_ordered c u v q h
  · rw [physicalValuation_ordered c v u q (lt_of_le_of_ne (le_of_not_gt h) hne.symm), c.color_symm v u]

theorem physicalValuation_ordered_false (c : Coloring) (u v : Vertex) (q : Color)
    (huv : u < v) :
    physicalValuation c (orderedEdgeVar u v q) = false ↔ c u v ≠ palette q := by
  rw [Bool.eq_false_iff]
  exact not_congr (physicalValuation_ordered c u v q huv)

def orderedPairs : List (Vertex × Vertex) :=
  (List.finRange 52).flatMap fun u =>
    ((List.finRange 52).filter fun v => u < v).map fun v => (u,v)

def oneHotClauses (u v : Vertex) : CNF :=
  [(List.finRange 4).map fun q => (true, orderedEdgeVar u v q)] ++
  (List.finRange 4).flatMap fun q =>
    ((List.finRange 4).filter fun r => q < r).map fun r =>
      [(false, orderedEdgeVar u v q), (false, orderedEdgeVar u v r)]

def physicalClauses : CNF := orderedPairs.flatMap fun pair => oneHotClauses pair.1 pair.2

def triangleClauses : CNF :=
  (List.finRange 52).flatMap fun u =>
    ((List.finRange 52).filter fun v => u < v).flatMap fun v =>
      ((List.finRange 52).filter fun w => v < w).flatMap fun w =>
        (List.finRange 4).map fun q =>
          [(false, orderedEdgeVar u v q), (false, orderedEdgeVar u w q),
           (false, orderedEdgeVar v w q)]

theorem physicalValuation_oneHot (c : Coloring) (u v : Vertex) (huv : u < v) :
    FormulaSat (physicalValuation c) (oneHotClauses u v) := by
  rw [oneHotClauses, formulaSat_append]
  constructor
  · intro clause hclause
    simp only [List.mem_singleton] at hclause
    subst clause
    obtain ⟨q,hq⟩ := palette_surjective (c u v)
    refine ⟨(true,orderedEdgeVar u v q), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨q,by simp,rfl⟩
    · exact (physicalValuation_ordered c u v q huv).2 hq.symm
  · intro clause hclause
    simp only [List.mem_flatMap, List.mem_map] at hclause
    obtain ⟨q,hq,r,hr,rfl⟩ := hclause
    have hqr : q < r := by simpa using (List.mem_filter.mp hr).2
    by_cases hcq : c u v = palette q
    · refine ⟨(false,orderedEdgeVar u v r),by simp,?_⟩
      apply (physicalValuation_ordered_false c u v r huv).2
      intro hcr
      have heq := palette_injective (hcq.symm.trans hcr)
      exact (ne_of_lt hqr) heq
    · exact ⟨(false,orderedEdgeVar u v q),by simp,
        (physicalValuation_ordered_false c u v q huv).2 hcq⟩

theorem physicalValuation_physical (c : Coloring) :
    FormulaSat (physicalValuation c) physicalClauses := by
  intro clause hclause
  obtain ⟨pair,hpair,hclause⟩ := List.mem_flatMap.mp hclause
  simp only [orderedPairs, List.mem_flatMap, List.mem_map] at hpair
  obtain ⟨u,hu,v,hv,rfl⟩ := hpair
  exact physicalValuation_oneHot c u v (by simpa using (List.mem_filter.mp hv).2) clause hclause

theorem physicalValuation_triangles (c : Coloring) (hc : NoMonochromaticTriangle c) :
    FormulaSat (physicalValuation c) triangleClauses := by
  intro clause hclause
  simp only [triangleClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨u,hu,v,hv,w,hw,q,hq,rfl⟩ := hclause
  have huv : u < v := by simpa using (List.mem_filter.mp hv).2
  have hvw : v < w := by simpa using (List.mem_filter.mp hw).2
  have huw : u < w := lt_trans huv hvw
  by_cases hab : c u v = palette q
  · by_cases hac : c u w = palette q
    · refine ⟨(false,orderedEdgeVar v w q),by simp,?_⟩
      apply (physicalValuation_ordered_false c v w q hvw).2
      intro hbc
      exact hc u v w ⟨ne_of_lt huv,ne_of_lt huw,ne_of_lt hvw⟩
        ⟨hab.trans hac.symm,hac.trans hbc.symm⟩
    · exact ⟨(false,orderedEdgeVar u w q),by simp,
        (physicalValuation_ordered_false c u w q huw).2 hac⟩
  · exact ⟨(false,orderedEdgeVar u v q),by simp,
      (physicalValuation_ordered_false c u v q huv).2 hab⟩


/-- Actual neighbors, in the same ascending order as the Python generator. -/
def neighborVertices (v : Vertex) : List Vertex :=
  (List.finRange 52).filter fun u => u ≠ v

@[simp] theorem mem_neighborVertices (v u : Vertex) :
    u ∈ neighborVertices v ↔ u ≠ v := by simp [neighborVertices]

set_option maxRecDepth 10000 in
theorem neighborVertices_length : ∀ v : Vertex, (neighborVertices v).length = 51 := by decide

def degreeInputs (v : Vertex) (q : Color) : List Nat :=
  (neighborVertices v).map fun u => edgeVar v u q

@[simp] theorem degreeInputs_length (v : Vertex) (q : Color) :
    (degreeInputs v q).length = 51 := by simp [degreeInputs, neighborVertices_length]

theorem degreeInputs_bound (v : Vertex) (q : Color) (atom : Nat)
    (h : atom ∈ degreeInputs v q) : atom < 5305 := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
  exact (edgeVar_bounds v u q ((mem_neighborVertices v u).mp hu).symm).2

theorem physical_degree_count (c : Coloring) (v : Vertex) (q : Color) :
    prefixCount (physicalValuation c) (degreeInputs v q) 51 = colorDegree c (palette q) v := by
  classical
  rw [prefixCount, ← degreeInputs_length v q, List.take_length, degreeInputs, List.countP_map]
  simp only [Function.comp_def]
  have heq : List.countP (fun u => physicalValuation c (edgeVar v u q)) (neighborVertices v) =
      List.countP (fun u => decide (c v u = palette q)) (neighborVertices v) := by
    apply List.countP_congr
    intro u hu
    simpa using physicalValuation_edge c v u q ((mem_neighborVertices v u).mp hu).symm
  rw [heq, List.countP_eq_length_filter]
  have hn : ((neighborVertices v).filter (fun u => decide (c v u = palette q))).Nodup :=
    ((List.nodup_finRange 52).filter (fun u => decide (u ≠ v))).filter
      (fun u => decide (c v u = palette q))
  have hset : ((neighborVertices v).filter (fun u => decide (c v u = palette q))).toFinset =
      colorNeighborhood c (palette q) v := by
    ext u
    simp [neighborVertices, colorNeighborhood, and_comm]
  rw [← List.toFinset_card_of_nodup hn, hset]
  rfl


end PricingABD.B52Core
