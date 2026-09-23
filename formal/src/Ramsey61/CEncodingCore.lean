import Ramsey61.Foundations
import Ramsey61.DenseCounter

/-!
# The physical and degree-counter core of the retained C encoding

All addresses here are the original DIMACS numbers from `encode.py`.
The host has all 61 vertices and no root normalization is required for this
core. H, profiles, selector clauses, root units and physical seeds are added
by later modules. No encoder or retained CNF is changed by this development.
-/

namespace Ramsey61.CEncodingCore
open DenseCounter

abbrev Vertex := Fin 61
abbrev Color := Fin 4
abbrev Coloring := EdgeColoring Vertex FourColor

def palette (q : Color) : FourColor :=
  (decide (2 ≤ q.val), decide (q.val % 2 = 1))

theorem palette_injective : Function.Injective palette := by decide

theorem palette_surjective : Function.Surjective palette := by
  rintro ⟨a,b⟩
  cases a <;> cases b
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩

/-- Start of the lexicographic unordered-edge row, exactly `u*(121-u)//2`. -/
def rowStart (u : Nat) : Nat := u * (121 - u) / 2

/- A small finite arithmetic table (61 by 61), not an assumed edge map. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem rowStart_separated : ∀ u v : Vertex, u < v →
    rowStart u.val + (60 - u.val) ≤ rowStart v.val := by decide

set_option maxRecDepth 10000 in
theorem rowStart_bounded : ∀ u : Vertex,
    rowStart u.val + (60 - u.val) ≤ 1830 := by decide

def edgeRank (u v : Vertex) : Nat := rowStart u.val + (v.val - u.val - 1)

def orderedEdgeVar (u v : Vertex) (q : Color) : Nat :=
  4 * edgeRank u v + q.val + 1

/-- Unordered-edge lookup used by degree input lists. -/
def edgeVar (u v : Vertex) (q : Color) : Nat :=
  if u < v then orderedEdgeVar u v q else orderedEdgeVar v u q

theorem edgeRank_bounds (u v : Vertex) (h : u < v) :
    rowStart u.val ≤ edgeRank u v ∧
      edgeRank u v < rowStart u.val + (60 - u.val) := by
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
    1 ≤ orderedEdgeVar u v q ∧ orderedEdgeVar u v q < 7321 := by
  have hb := edgeRank_bounds u v huv
  have hs := rowStart_bounded u
  have hq := q.isLt
  unfold orderedEdgeVar
  omega

/-- The left-associated integer expression in Python, on its valid domain. -/
theorem orderedEdgeVar_python_formula (u v : Vertex) (q : Color) (huv : u < v) :
    orderedEdgeVar u v q =
      4 * (u.val * (122 - u.val - 1) / 2 + v.val - u.val - 1) + q.val + 1 := by
  have hu := u.isLt
  change u.val < v.val at huv
  have hsub : 122 - u.val - 1 = 121 - u.val := by omega
  rw [hsub]
  unfold orderedEdgeVar edgeRank rowStart
  omega

theorem edgeVar_bounds (u v : Vertex) (q : Color) (hne : u ≠ v) :
    1 ≤ edgeVar u v q ∧ edgeVar u v q < 7321 := by
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
  (List.finRange 61).flatMap fun u =>
    ((List.finRange 61).filter fun v => u < v).map fun v => (u,v)

def oneHotClauses (u v : Vertex) : CNF :=
  [(List.finRange 4).map fun q => (true, orderedEdgeVar u v q)] ++
  (List.finRange 4).flatMap fun q =>
    ((List.finRange 4).filter fun r => q < r).map fun r =>
      [(false, orderedEdgeVar u v q), (false, orderedEdgeVar u v r)]

def physicalClauses : CNF := orderedPairs.flatMap fun pair => oneHotClauses pair.1 pair.2

def triangleClauses : CNF :=
  (List.finRange 61).flatMap fun u =>
    ((List.finRange 61).filter fun v => u < v).flatMap fun v =>
      ((List.finRange 61).filter fun w => v < w).flatMap fun w =>
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
  (List.finRange 61).filter fun u => u ≠ v

@[simp] theorem mem_neighborVertices (v u : Vertex) :
    u ∈ neighborVertices v ↔ u ≠ v := by simp [neighborVertices]

set_option maxRecDepth 10000 in
theorem neighborVertices_length : ∀ v : Vertex, (neighborVertices v).length = 60 := by decide

def degreeInputs (v : Vertex) (q : Color) : List Nat :=
  (neighborVertices v).map fun u => edgeVar v u q

@[simp] theorem degreeInputs_length (v : Vertex) (q : Color) :
    (degreeInputs v q).length = 60 := by simp [degreeInputs, neighborVertices_length]

theorem degreeInputs_bound (v : Vertex) (q : Color) (atom : Nat)
    (h : atom ∈ degreeInputs v q) : atom < 7321 := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
  exact (edgeVar_bounds v u q ((mem_neighborVertices v u).mp hu).symm).2

theorem physical_degree_count (c : Coloring) (v : Vertex) (q : Color) :
    prefixCount (physicalValuation c) (degreeInputs v q) 60 = colorDegree c (palette q) v := by
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
    ((List.nodup_finRange 61).filter (fun u => decide (u ≠ v))).filter
      (fun u => decide (c v u = palette q))
  have hset : ((neighborVertices v).filter (fun u => decide (c v u = palette q))).toFinset =
      colorNeighborhood c (palette q) v := by
    ext u
    simp [neighborVertices, colorNeighborhood, and_comm]
  rw [← List.toFinset_card_of_nodup hn, hset]
  rfl

/-- 244 consecutive rectangles, each exactly60 rows by17 thresholds. -/
def degreeStart (v : Vertex) (q : Color) : Nat :=
  7321 + (4 * v.val + q.val) * 1020

theorem degreeAtom_bounds (v : Vertex) (q : Color) (row column : Nat)
    (hrow : row < 60) (hcolumn : column < 17) :
    7321 ≤ denseAtom (degreeStart v q) 17 row column ∧
      denseAtom (degreeStart v q) 17 row column < 256201 := by
  have hv := v.isLt
  have hq := q.isLt
  unfold denseAtom degreeStart
  omega

theorem degreeAtom_injective (v w : Vertex) (q r : Color)
    (row column row' column' : Nat)
    (hrow : row < 60) (hcolumn : column < 17)
    (hrow' : row' < 60) (hcolumn' : column' < 17)
    (heq : denseAtom (degreeStart v q) 17 row column =
      denseAtom (degreeStart w r) 17 row' column') :
    v = w ∧ q = r ∧ row = row' ∧ column = column' := by
  have hv := v.isLt
  have hw := w.isLt
  have hq := q.isLt
  have hr := r.isLt
  unfold denseAtom degreeStart at heq
  have ev : v.val = w.val := by omega
  have eq : q.val = r.val := by omega
  exact ⟨Fin.ext ev, Fin.ext eq, by omega, by omega⟩

theorem degreeAtom_python_formula (v : Vertex) (q : Color) (row column : Nat) :
    denseAtom (degreeStart v q) 17 row column =
      7321 + (4 * v.val + q.val) * 60 * 17 + row * 17 + column := by
  unfold denseAtom degreeStart
  omega

def degreeVertex (atom : Nat) : Vertex :=
  ⟨((atom - 7321) / 1020 / 4) % 61, Nat.mod_lt _ (by decide)⟩

def degreeColor (atom : Nat) : Color :=
  ⟨((atom - 7321) / 1020) % 4, Nat.mod_lt _ (by decide)⟩

/-- Simultaneously assign every degree auxiliary from the original host's
physical bits. These244 rectangles exhaust7321..256200 and cannot change an
edge bit. The modulo61 in the total decoder is irrelevant inside this range. -/
noncomputable def coreValuation (c : Coloring) : Valuation := fun atom =>
  if 7321 ≤ atom ∧ atom < 256201 then
    decide ((atom - 7321) % 17 + 1 ≤
      prefixCount (physicalValuation c) (degreeInputs (degreeVertex atom) (degreeColor atom))
        ((atom - 7321) % 1020 / 17 + 1))
  else physicalValuation c atom

theorem coreValuation_eq_physical (c : Coloring) (atom : Nat) (h : atom < 7321) :
    coreValuation c atom = physicalValuation c atom := by
  have hn : ¬ (7321 ≤ atom ∧ atom < 256201) := by omega
  simp [coreValuation, hn]

theorem coreValuation_degree (c : Coloring) (v : Vertex) (q : Color) (row column : Nat)
    (hrow : row < 60) (hcolumn : column < 17) :
    coreValuation c (denseAtom (degreeStart v q) 17 row column) =
      decide (column + 1 ≤ prefixCount (physicalValuation c) (degreeInputs v q) (row + 1)) := by
  have hv := v.isLt
  have hq := q.isLt
  let atom := denseAtom (degreeStart v q) 17 row column
  have hrange : 7321 ≤ atom ∧ atom < 256201 := by dsimp [atom, denseAtom, degreeStart]; omega
  have hblock : (atom - 7321) / 1020 = 4 * v.val + q.val := by
    dsimp [atom, denseAtom, degreeStart]; omega
  have hr : (atom - 7321) % 1020 / 17 = row := by
    dsimp [atom, denseAtom, degreeStart]; omega
  have hk : (atom - 7321) % 17 = column := by
    dsimp [atom, denseAtom, degreeStart]; omega
  have hvertex : degreeVertex atom = v := by
    apply Fin.ext
    change ((atom - 7321) / 1020 / 4) % 61 = v.val
    rw [hblock]
    omega
  have hcolor : degreeColor atom = q := by
    apply Fin.ext
    change ((atom - 7321) / 1020) % 4 = q.val
    rw [hblock]
    omega
  change coreValuation c atom = _
  rw [coreValuation, if_pos hrange, hvertex, hcolor, hr, hk]

theorem coreValuation_realizes_degree (c : Coloring) (v : Vertex) (q : Color) :
    Realizes (coreValuation c) (degreeInputs v q) (degreeStart v q) 17 := by
  intro row hrow column hcolumn
  have hr : row < 60 := by simpa using hrow
  rw [coreValuation_degree c v q row column hr hcolumn]
  have heq := prefixCount_congr (coreValuation c) (physicalValuation c) (degreeInputs v q)
    (fun atom hmem => coreValuation_eq_physical c atom (degreeInputs_bound v q atom hmem))
    (row + 1)
  rw [heq]

def degreeClauses : CNF :=
  (List.finRange 61).flatMap fun v =>
    (List.finRange 4).flatMap fun q => counterCNF (degreeInputs v q) (degreeStart v q) 17

def degreeCapClauses : CNF :=
  (List.finRange 61).flatMap fun v =>
    (List.finRange 4).map fun q => [(false, denseAtom (degreeStart v q) 17 59 16)]

theorem coreValuation_degreeClauses (c : Coloring) :
    FormulaSat (coreValuation c) degreeClauses := by
  intro clause hclause
  obtain ⟨v,hv,hclause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨q,hq,hclause⟩ := List.mem_flatMap.mp hclause
  exact counterCNF_satisfied_of_realizes _ _ _ _
    (coreValuation_realizes_degree c v q) clause hclause

theorem coreValuation_degreeCaps (c : Coloring) (hc : NoMonochromaticTriangle c) :
    FormulaSat (coreValuation c) degreeCapClauses := by
  intro clause hclause
  obtain ⟨v,hv,hclause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hclause
  refine ⟨(false,denseAtom (degreeStart v q) 17 59 16),by simp,?_⟩
  rw [coreValuation_degree c v q 59 16 (by decide) (by decide)]
  have hcount := physical_degree_count c v q
  have hcap := fourColor_colorDegree_le_sixteen c hc (palette q) v
  simp [hcount, show ¬ 17 ≤ colorDegree c (palette q) v by omega]

/-- A common transfer lemma for already proved physical clause families. -/
theorem coreValuation_preserves_physical (c : Coloring) (formula : CNF)
    (hbound : ∀ clause ∈ formula, ∀ literal ∈ clause, literal.2 < 7321)
    (hsat : FormulaSat (physicalValuation c) formula) :
    FormulaSat (coreValuation c) formula := by
  intro clause hclause
  obtain ⟨literal,hl,htrue⟩ := hsat clause hclause
  refine ⟨literal,hl,?_⟩
  rw [coreValuation_eq_physical c literal.2 (hbound clause hclause literal hl)]
  exact htrue

theorem oneHotClauses_bound (u v : Vertex) (huv : u < v) :
    ∀ clause ∈ oneHotClauses u v, ∀ literal ∈ clause, literal.2 < 7321 := by
  intro clause hclause literal hliteral
  rcases List.mem_append.mp hclause with hfirst | hrest
  · simp only [List.mem_singleton] at hfirst
    subst clause
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hliteral
    exact (orderedEdgeVar_bounds u v q huv).2
  · obtain ⟨q,hq,hclause⟩ := List.mem_flatMap.mp hrest
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hclause
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
    rcases hliteral with rfl | rfl
    · exact (orderedEdgeVar_bounds u v q huv).2
    · exact (orderedEdgeVar_bounds u v r huv).2

theorem physicalClauses_bound :
    ∀ clause ∈ physicalClauses, ∀ literal ∈ clause, literal.2 < 7321 := by
  intro clause hclause literal hliteral
  obtain ⟨pair,hpair,hclause⟩ := List.mem_flatMap.mp hclause
  simp only [orderedPairs, List.mem_flatMap, List.mem_map] at hpair
  obtain ⟨u,hu,v,hv,rfl⟩ := hpair
  exact oneHotClauses_bound u v (by simpa using (List.mem_filter.mp hv).2) clause hclause literal hliteral

theorem triangleClauses_bound :
    ∀ clause ∈ triangleClauses, ∀ literal ∈ clause, literal.2 < 7321 := by
  intro clause hclause literal hliteral
  simp only [triangleClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨u,hu,v,hv,w,hw,q,hq,rfl⟩ := hclause
  have huv : u < v := by simpa using (List.mem_filter.mp hv).2
  have hvw : v < w := by simpa using (List.mem_filter.mp hw).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
  rcases hliteral with rfl | rfl | rfl
  · exact (orderedEdgeVar_bounds u v q huv).2
  · exact (orderedEdgeVar_bounds u w q (lt_trans huv hvw)).2
  · exact (orderedEdgeVar_bounds v w q hvw).2

/-- Exactly the first four retained base families, in producer order. -/
def coreCNF : CNF :=
  physicalClauses ++ triangleClauses ++ degreeClauses ++ degreeCapClauses

/-- No auxiliary-realization or address-injectivity hypothesis remains: the
witness is constructed directly from any actual good61-vertex host. -/
theorem coloring_satisfies_core (c : Coloring) (hc : NoMonochromaticTriangle c) :
    FormulaSat (coreValuation c) coreCNF := by
  simp only [coreCNF, formulaSat_append]
  exact ⟨⟨⟨coreValuation_preserves_physical c physicalClauses physicalClauses_bound
      (physicalValuation_physical c),
    coreValuation_preserves_physical c triangleClauses triangleClauses_bound
      (physicalValuation_triangles c hc)⟩,
    coreValuation_degreeClauses c⟩, coreValuation_degreeCaps c hc⟩

theorem core_satisfiable_of_good_coloring (c : Coloring) (hc : NoMonochromaticTriangle c) :
    ∃ assignment : Nat → Bool,
      ∀ clause ∈ coreCNF, ∃ literal ∈ clause, assignment literal.2 = literal.1 := by
  exact ⟨coreValuation c, coloring_satisfies_core c hc⟩

end Ramsey61.CEncodingCore
