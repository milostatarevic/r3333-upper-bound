import Ramsey61.CEncodingCore
import Ramsey61.Selector

/-!
# All ten deterministic families of the retained broader C base

The original variable numbers, input orders, profile order and clauses are
preserved. This module does not add the removed opposite-high or small-fiber
restrictions. The physical456 seed cover is a separate mathematical input.
-/
namespace Ramsey61.CEncodingBase
open DenseCounter CEncodingCore

inductive Family where | A | B | C | D | E deriving DecidableEq

def profileData (i : Fin 35) : Family × (Color → Nat) :=
  match i.val with
  | 0 => (.A, ![12, 16, 16, 16])
  | 1 => (.A, ![16, 12, 16, 16])
  | 2 => (.A, ![16, 16, 12, 16])
  | 3 => (.A, ![16, 16, 16, 12])
  | 4 => (.B, ![13, 15, 16, 16])
  | 5 => (.B, ![13, 16, 15, 16])
  | 6 => (.B, ![13, 16, 16, 15])
  | 7 => (.B, ![15, 13, 16, 16])
  | 8 => (.B, ![15, 16, 13, 16])
  | 9 => (.B, ![15, 16, 16, 13])
  | 10 => (.B, ![16, 13, 15, 16])
  | 11 => (.B, ![16, 13, 16, 15])
  | 12 => (.B, ![16, 15, 13, 16])
  | 13 => (.B, ![16, 15, 16, 13])
  | 14 => (.B, ![16, 16, 13, 15])
  | 15 => (.B, ![16, 16, 15, 13])
  | 16 => (.C, ![14, 14, 16, 16])
  | 17 => (.C, ![14, 16, 14, 16])
  | 18 => (.C, ![14, 16, 16, 14])
  | 19 => (.C, ![16, 14, 14, 16])
  | 20 => (.C, ![16, 14, 16, 14])
  | 21 => (.C, ![16, 16, 14, 14])
  | 22 => (.D, ![14, 15, 15, 16])
  | 23 => (.D, ![14, 15, 16, 15])
  | 24 => (.D, ![14, 16, 15, 15])
  | 25 => (.D, ![15, 14, 15, 16])
  | 26 => (.D, ![15, 14, 16, 15])
  | 27 => (.D, ![15, 15, 14, 16])
  | 28 => (.D, ![15, 15, 16, 14])
  | 29 => (.D, ![15, 16, 14, 15])
  | 30 => (.D, ![15, 16, 15, 14])
  | 31 => (.D, ![16, 14, 15, 15])
  | 32 => (.D, ![16, 15, 14, 15])
  | 33 => (.D, ![16, 15, 15, 14])
  | _ => (.E, ![15, 15, 15, 15])

def profileTuple (i : Fin 35) : FourDegreeTuple :=
  ((profileData i).2 0, (profileData i).2 1, (profileData i).2 2, (profileData i).2 3)

set_option maxRecDepth 10000 in
theorem profileData_bounds : ∀ i q, 12 ≤ (profileData i).2 q ∧ (profileData i).2 q ≤ 16 := by decide

set_option maxRecDepth 10000 in
theorem profileData_covers : ∀ t ∈ degreeTargets61, ∃ i, profileTuple i = t := by decide

def familyMass : Family → Nat | .A => 48 | .B => 47 | .C => 32 | .D => 46 | .E => 60

set_option maxRecDepth 10000 in
theorem profileData_mass : ∀ i, mass4 ((profileData i).2 0) ((profileData i).2 1)
    ((profileData i).2 2) ((profileData i).2 3) = familyMass (profileData i).1 := by decide

def ProfileExact (c : Coloring) (v : Vertex) (i : Fin 35) : Prop :=
  ∀ q : Color, colorDegree c (palette q) v = (profileData i).2 q

instance (c : Coloring) (v : Vertex) (i : Fin 35) : Decidable (ProfileExact c v i) :=
  inferInstanceAs (Decidable (∀ q : Color, colorDegree c (palette q) v = (profileData i).2 q))

def neighborAt (v : Vertex) (slot : Fin 60) : Vertex :=
  ⟨if slot.val < v.val then slot.val else slot.val + 1, by split_ifs <;> omega⟩

def highVar (v u : Vertex) : Nat :=
  256201 + v.val * 60 + (if u.val < v.val then u.val else u.val - 1)

def hStart (v : Vertex) : Nat := 259861 + v.val * 2880

def hInputs (v : Vertex) : List Nat := (neighborVertices v).map (highVar v)

@[simp] theorem hInputs_length (v : Vertex) : (hInputs v).length = 60 := by
  simp [hInputs, neighborVertices_length]

def rootBlocks (q : Color) : List Vertex :=
  (List.finRange 61).filter fun u =>
    if q = 0 then 1 ≤ u.val ∧ u.val ≤ 16
    else if q = 1 then 17 ≤ u.val ∧ u.val ≤ 32
    else if q = 2 then 33 ≤ u.val ∧ u.val ≤ 46
    else 47 ≤ u.val ∧ u.val ≤ 60

set_option maxRecDepth 10000 in
theorem rootBlocks_no_root : ∀ q u, u ∈ rootBlocks q → (0 : Vertex) ≠ u := by decide

set_option maxRecDepth 10000 in
theorem rootBlocks_high_length : (rootBlocks 0).length = 16 ∧ (rootBlocks 1).length = 16 := by decide

def fiberVertex (i : Fin 32) : Vertex := ⟨i.val + 1, by omega⟩
def fiberColor (i : Fin 32) : Color := if i.val < 16 then 0 else 1

def fiberTargets (i : Fin 32) : List Vertex := rootBlocks (if i.val < 16 then 1 else 0)
def fiberInputs (i : Fin 32) : List Nat :=
  (fiberTargets i).map fun u => edgeVar (fiberVertex i) u (fiberColor i)

def fiberStart (i : Fin 32) : Nat := 435541 + i.val * 64

theorem fiberInputs_length (i : Fin 32) : (fiberInputs i).length = 16 := by
  simp only [fiberInputs, List.length_map, fiberTargets]
  split_ifs <;> simp [rootBlocks_high_length]

set_option maxRecDepth 10000 in
theorem fiberTargets_distinct : ∀ i u, u ∈ fiberTargets i → fiberVertex i ≠ u := by decide

def profileVar (v : Vertex) (i : Fin 35) : Nat := 437589 + v.val * 35 + i.val

def highVertex (atom : Nat) : Vertex := ⟨((atom - 256201) / 60) % 61, Nat.mod_lt _ (by decide)⟩
def highSlot (atom : Nat) : Fin 60 := ⟨(atom - 256201) % 60, Nat.mod_lt _ (by decide)⟩
def hVertex (atom : Nat) : Vertex := ⟨((atom - 259861) / 2880) % 61, Nat.mod_lt _ (by decide)⟩
def fiberIndex (atom : Nat) : Fin 32 := ⟨((atom - 435541) / 64) % 32, Nat.mod_lt _ (by decide)⟩
def profileVertex (atom : Nat) : Vertex := ⟨((atom - 437589) / 35) % 61, Nat.mod_lt _ (by decide)⟩
def profileIndex (atom : Nat) : Fin 35 := ⟨(atom - 437589) % 35, Nat.mod_lt _ (by decide)⟩

/-- One valuation on all variables; its semantic highness uses the neighbor's
full degree in the actual joining color. -/
noncomputable def baseValuation (c : Coloring) : Valuation := by
  classical
  exact fun atom =>
    if 256201 ≤ atom ∧ atom < 259861 then
      let v := highVertex atom
      let u := neighborAt v (highSlot atom)
      decide (15 ≤ colorDegree c (c v u) u)
    else if 259861 ≤ atom ∧ atom < 435541 then
      decide ((atom - 259861) % 48 + 1 ≤
        List.countP (fun u => decide (15 ≤ colorDegree c (c (hVertex atom) u) u))
          ((neighborVertices (hVertex atom)).take ((atom - 259861) % 2880 / 48 + 1)))
    else if 435541 ≤ atom ∧ atom < 437589 then
      decide ((atom - 435541) % 4 + 1 ≤
        prefixCount (physicalValuation c) (fiberInputs (fiberIndex atom))
          ((atom - 435541) % 64 / 4 + 1))
    else if 437589 ≤ atom ∧ atom < 439724 then
      decide (ProfileExact c (profileVertex atom) (profileIndex atom))
    else coreValuation c atom

theorem baseValuation_core (c : Coloring) (atom : Nat) (h : atom < 256201) :
    baseValuation c atom = coreValuation c atom := by
  have h1 : ¬ (256201 ≤ atom ∧ atom < 259861) := by omega
  have h2 : ¬ (259861 ≤ atom ∧ atom < 435541) := by omega
  have h3 : ¬ (435541 ≤ atom ∧ atom < 437589) := by omega
  have h4 : ¬ (437589 ≤ atom ∧ atom < 439724) := by omega
  simp [baseValuation,h1,h2,h3,h4]

theorem baseValuation_physical (c : Coloring) (atom : Nat) (h : atom < 7321) :
    baseValuation c atom = physicalValuation c atom := by
  rw [baseValuation_core c atom (by omega),coreValuation_eq_physical c atom h]

theorem baseValuation_degree (c : Coloring) (v : Vertex) (q : Color) (row column : Nat)
    (hr : row < 60) (hk : column < 17) :
    baseValuation c (denseAtom (degreeStart v q) 17 row column) =
      decide (column + 1 ≤ prefixCount (physicalValuation c) (degreeInputs v q) (row + 1)) := by
  rw [baseValuation_core c _ (degreeAtom_bounds v q row column hr hk).2,
    coreValuation_degree c v q row column hr hk]

theorem baseValuation_degree_terminal (c : Coloring) (v : Vertex) (q : Color) (k : Nat)
    (hk : k < 17) :
    baseValuation c (denseAtom (degreeStart v q) 17 59 k) =
      decide (k + 1 ≤ colorDegree c (palette q) v) := by
  rw [baseValuation_degree c v q 59 k (by decide) hk]
  simp only [show 59+1=60 by decide,physical_degree_count]

theorem highVar_bounds (v u : Vertex) (hne : v ≠ u) :
    256201 ≤ highVar v u ∧ highVar v u < 259861 := by
  have hv := v.isLt
  have hu := u.isLt
  have hne' : v.val ≠ u.val := Fin.val_ne_of_ne hne
  unfold highVar
  split_ifs <;> omega

theorem baseValuation_high (c : Coloring) (v u : Vertex) (hne : v ≠ u) :
    baseValuation c (highVar v u) = decide (15 ≤ colorDegree c (c v u) u) := by
  have hv := v.isLt
  have hu := u.isLt
  have hne' : v.val ≠ u.val := Fin.val_ne_of_ne hne
  have hrange := highVar_bounds v u hne
  have hvdecode : highVertex (highVar v u) = v := by
    apply Fin.ext
    simp only [highVertex,highVar]
    split_ifs <;> omega
  have hudecode : neighborAt v (highSlot (highVar v u)) = u := by
    apply Fin.ext
    simp only [neighborAt,highSlot,highVar]
    split_ifs <;> omega
  rw [baseValuation,if_pos hrange,hvdecode]
  dsimp
  rw [hudecode]

/-- Generic preservation interface for a previously established physical family. -/
theorem preserves_formula_below (c : Coloring) (formula : CNF)
    (hbound : ∀ clause ∈ formula, ∀ l ∈ clause, l.2 < 7321)
    (hs : FormulaSat (physicalValuation c) formula) : FormulaSat (baseValuation c) formula := by
  intro clause hclause
  obtain ⟨l,hl,ht⟩ := hs clause hclause
  exact ⟨l,hl,by rw [baseValuation_physical c l.2 (hbound clause hclause l hl)]; exact ht⟩

theorem baseValuation_realizes_degree (c : Coloring) (v : Vertex) (q : Color) :
    Realizes (baseValuation c) (degreeInputs v q) (degreeStart v q) 17 := by
  intro row hr column hk
  have hr' : row < 60 := by simpa using hr
  rw [baseValuation_degree c v q row column hr' hk]
  rw [prefixCount_congr (baseValuation c) (physicalValuation c) (degreeInputs v q)
    (fun atom h => baseValuation_physical c atom (degreeInputs_bound v q atom h))]

theorem baseValuation_coreCNF (c : Coloring) (hc : NoMonochromaticTriangle c) :
    FormulaSat (baseValuation c) coreCNF := by
  simp only [coreCNF,formulaSat_append]
  refine ⟨⟨⟨preserves_formula_below c _ physicalClauses_bound (physicalValuation_physical c),
    preserves_formula_below c _ triangleClauses_bound (physicalValuation_triangles c hc)⟩,?_⟩,?_⟩
  · intro clause hclause
    obtain ⟨v,hv,hclause⟩ := List.mem_flatMap.mp hclause
    obtain ⟨q,hq,hclause⟩ := List.mem_flatMap.mp hclause
    exact counterCNF_satisfied_of_realizes _ _ _ _ (baseValuation_realizes_degree c v q) clause hclause
  · intro clause hclause
    obtain ⟨v,hv,hclause⟩ := List.mem_flatMap.mp hclause
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hclause
    refine ⟨(false,denseAtom (degreeStart v q) 17 59 16),by simp,?_⟩
    rw [baseValuation_degree_terminal c v q 16 (by decide)]
    have hcap := fourColor_colorDegree_le_sixteen c hc (palette q) v
    simp [show ¬17≤colorDegree c (palette q) v by omega]

def highnessClauses : CNF :=
  (List.finRange 61).flatMap fun v => (neighborVertices v).flatMap fun u =>
    (List.finRange 4).flatMap fun q =>
      [[(false,edgeVar v u q),(false,highVar v u),(true,denseAtom (degreeStart u q) 17 59 14)],
       [(false,edgeVar v u q),(true,highVar v u),(false,denseAtom (degreeStart u q) 17 59 14)]]

theorem baseValuation_highnessClauses (c : Coloring) :
    FormulaSat (baseValuation c) highnessClauses := by
  intro clause hclause
  simp only [highnessClauses,List.mem_flatMap] at hclause
  obtain ⟨v,hv,u,hu,q,hq,hclause⟩ := hclause
  have hne : v ≠ u := ((mem_neighborVertices v u).mp hu).symm
  have hedge := physicalValuation_edge c v u q hne
  have hbound := (edgeVar_bounds v u q hne).2
  have hh := baseValuation_high c v u hne
  have hd := baseValuation_degree_terminal c u q 14 (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hclause
  rcases hclause with rfl | rfl
  all_goals
    by_cases he : c v u = palette q
    · rw [he] at hh
      simp [ClauseSat,hh,hd]
      omega
    · refine ⟨(false,edgeVar v u q),by simp,?_⟩
      rw [baseValuation_physical c _ hbound,Bool.eq_false_iff]
      exact fun h => he (hedge.mp h)


theorem hInputs_prefix (c : Coloring) (v : Vertex) (n : Nat) :
    prefixCount (baseValuation c) (hInputs v) n =
      List.countP (fun u => decide (15 ≤ colorDegree c (c v u) u)) ((neighborVertices v).take n) := by
  classical
  simp only [prefixCount,hInputs,←List.map_take,List.countP_map,Function.comp_def]
  apply List.countP_congr
  intro u hu
  have hne : v ≠ u := ((mem_neighborVertices v u).mp (List.mem_of_mem_take hu)).symm
  rw [baseValuation_high c v u hne]

theorem hInputs_count (c : Coloring) (v : Vertex) :
    prefixCount (baseValuation c) (hInputs v) 60 = H c v := by
  classical
  rw [hInputs_prefix,←neighborVertices_length v,List.take_length,List.countP_eq_length_filter]
  have hn : ((neighborVertices v).filter (fun u => decide (15 ≤ colorDegree c (c v u) u))).Nodup :=
    ((List.nodup_finRange 61).filter (fun u => decide (u ≠ v))).filter _
  have hset : ((neighborVertices v).filter (fun u => decide (15 ≤ colorDegree c (c v u) u))).toFinset =
      highOwnNeighborSupport c v := by
    ext u
    simp [neighborVertices,highOwnNeighborSupport,and_comm]
  rw [←List.toFinset_card_of_nodup hn,hset]
  rfl

theorem baseValuation_H (c : Coloring) (v : Vertex) (row column : Nat)
    (hr : row < 60) (hk : column < 48) :
    baseValuation c (denseAtom (hStart v) 48 row column) =
      decide (column+1 ≤ prefixCount (baseValuation c) (hInputs v) (row+1)) := by
  classical
  have hv := v.isLt
  let atom := denseAtom (hStart v) 48 row column
  have h1 : ¬(256201 ≤ atom ∧ atom < 259861) := by dsimp [atom,denseAtom,hStart]; omega
  have h2 : 259861 ≤ atom ∧ atom < 435541 := by dsimp [atom,denseAtom,hStart]; omega
  have hvertex : hVertex atom = v := by
    apply Fin.ext
    simp only [hVertex,atom,denseAtom,hStart]
    omega
  have hrdecode : (atom-259861)%2880/48 = row := by dsimp [atom,denseAtom,hStart]; omega
  have hkdecode : (atom-259861)%48 = column := by dsimp [atom,denseAtom,hStart]; omega
  change baseValuation c atom = _
  rw [baseValuation,if_neg h1,if_pos h2,hvertex,hrdecode,hkdecode,hInputs_prefix]

theorem baseValuation_H_terminal (c : Coloring) (v : Vertex) (k : Nat) (hk : k < 48) :
    baseValuation c (denseAtom (hStart v) 48 59 k) = decide (k+1 ≤ H c v) := by
  rw [baseValuation_H c v 59 k (by decide) hk]
  simp only [show 59+1=60 by decide,hInputs_count]

def HClauses : CNF := (List.finRange 61).flatMap fun v => counterCNF (hInputs v) (hStart v) 48

theorem baseValuation_HClauses (c : Coloring) : FormulaSat (baseValuation c) HClauses := by
  intro clause hclause
  obtain ⟨v,hv,hclause⟩ := List.mem_flatMap.mp hclause
  apply counterCNF_satisfied_of_realizes _ _ _ _ ?_ clause hclause
  intro row hr column hk
  exact baseValuation_H c v row column (by simpa using hr) hk

theorem fiberInputs_bound (i : Fin 32) (atom : Nat) (h : atom ∈ fiberInputs i) : atom < 7321 := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
  exact (edgeVar_bounds _ _ _ (fiberTargets_distinct i u hu)).2

theorem baseValuation_fiber (c : Coloring) (i : Fin 32) (row column : Nat)
    (hr : row < 16) (hk : column < 4) :
    baseValuation c (denseAtom (fiberStart i) 4 row column) =
      decide (column+1 ≤ prefixCount (physicalValuation c) (fiberInputs i) (row+1)) := by
  have hi := i.isLt
  let atom := denseAtom (fiberStart i) 4 row column
  have h1 : ¬(256201 ≤ atom ∧ atom < 259861) := by dsimp [atom,denseAtom,fiberStart]; omega
  have h2 : ¬(259861 ≤ atom ∧ atom < 435541) := by dsimp [atom,denseAtom,fiberStart]; omega
  have h3 : 435541 ≤ atom ∧ atom < 437589 := by dsimp [atom,denseAtom,fiberStart]; omega
  have hindex : fiberIndex atom = i := by
    apply Fin.ext
    simp only [fiberIndex,atom,denseAtom,fiberStart]
    omega
  have hrdecode : (atom-435541)%64/4 = row := by dsimp [atom,denseAtom,fiberStart]; omega
  have hkdecode : (atom-435541)%4 = column := by dsimp [atom,denseAtom,fiberStart]; omega
  change baseValuation c atom = _
  rw [baseValuation,if_neg h1,if_neg h2,if_pos h3,hindex,hrdecode,hkdecode]

def fiberClauses : CNF := (List.finRange 32).flatMap fun i => counterCNF (fiberInputs i) (fiberStart i) 4

theorem baseValuation_fiberClauses (c : Coloring) : FormulaSat (baseValuation c) fiberClauses := by
  intro clause hclause
  obtain ⟨i,hi,hclause⟩ := List.mem_flatMap.mp hclause
  apply counterCNF_satisfied_of_realizes _ _ _ _ ?_ clause hclause
  intro row hr column hk
  rw [baseValuation_fiber c i row column (by simpa [fiberInputs_length] using hr) hk]
  rw [prefixCount_congr (baseValuation c) (physicalValuation c) (fiberInputs i)
    (fun atom h => baseValuation_physical c atom (fiberInputs_bound i atom h))]

theorem baseValuation_profile (c : Coloring) (v : Vertex) (i : Fin 35) :
    baseValuation c (profileVar v i) = decide (ProfileExact c v i) := by
  classical
  have hv := v.isLt
  have hi := i.isLt
  let atom := profileVar v i
  have h1 : ¬(256201 ≤ atom ∧ atom < 259861) := by dsimp [atom,profileVar]; omega
  have h2 : ¬(259861 ≤ atom ∧ atom < 435541) := by dsimp [atom,profileVar]; omega
  have h3 : ¬(435541 ≤ atom ∧ atom < 437589) := by dsimp [atom,profileVar]; omega
  have h4 : 437589 ≤ atom ∧ atom < 439724 := by dsimp [atom,profileVar]; omega
  have hvertex : profileVertex atom = v := by
    apply Fin.ext
    simp only [profileVertex,atom,profileVar]
    omega
  have hindex : profileIndex atom = i := by
    apply Fin.ext
    simp only [profileIndex,atom,profileVar]
    omega
  change baseValuation c atom = _
  rw [baseValuation,if_neg h1,if_neg h2,if_neg h3,if_pos h4,hvertex,hindex]


def profileBounds (v : Vertex) (i : Fin 35) : List Literal :=
  (List.finRange 4).flatMap fun q =>
    [(true,denseAtom (degreeStart v q) 17 59 ((profileData i).2 q - 1)),
     (false,denseAtom (degreeStart v q) 17 59 ((profileData i).2 q))]

theorem profileBounds_all_iff (c : Coloring) (v : Vertex) (i : Fin 35) :
    (∀ l ∈ profileBounds v i, baseValuation c l.2 = l.1) ↔ ProfileExact c v i := by
  constructor
  · intro h q
    have hb := profileData_bounds i q
    have hp := h (true,denseAtom (degreeStart v q) 17 59 ((profileData i).2 q - 1))
      (List.mem_flatMap.mpr ⟨q,by simp,by simp⟩)
    have hn := h (false,denseAtom (degreeStart v q) 17 59 ((profileData i).2 q))
      (List.mem_flatMap.mpr ⟨q,by simp,by simp⟩)
    change baseValuation c (denseAtom (degreeStart v q) 17 59 ((profileData i).2 q - 1)) = true at hp
    change baseValuation c (denseAtom (degreeStart v q) 17 59 ((profileData i).2 q)) = false at hn
    rw [baseValuation_degree_terminal c v q _ (by omega)] at hp
    rw [baseValuation_degree_terminal c v q _ (by omega)] at hn
    simp only [decide_eq_true_eq,decide_eq_false_iff_not] at hp hn
    omega
  · intro h l hl
    obtain ⟨q,hq,hl⟩ := List.mem_flatMap.mp hl
    have hb := profileData_bounds i q
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl
    · rw [baseValuation_degree_terminal c v q _ (by omega)]
      simp [h q,show (profileData i).2 q - 1 + 1 = (profileData i).2 q by omega]
    · rw [baseValuation_degree_terminal c v q _ (by omega)]
      simp [h q]

def conjunctionClauses (indicator : Nat) (bounds : List Literal) : CNF :=
  (bounds.map fun bound => [(false,indicator),bound]) ++
    [[(true,indicator)] ++ bounds.map flip]

theorem conjunctionClauses_sat (assignment : Valuation) (indicator : Nat) (bounds : List Literal)
    (heq : assignment indicator = true ↔ ∀ l ∈ bounds, assignment l.2 = l.1) :
    FormulaSat assignment (conjunctionClauses indicator bounds) := by
  classical
  rw [conjunctionClauses,formulaSat_append]
  constructor
  · intro clause hclause
    obtain ⟨bound,hbound,rfl⟩ := List.mem_map.mp hclause
    by_cases hi : assignment indicator = true
    · exact ⟨bound,by simp,(heq.mp hi) bound hbound⟩
    · exact ⟨(false,indicator),by simp,Bool.eq_false_iff.mpr hi⟩
  · intro clause hclause
    simp only [List.mem_singleton] at hclause
    subst clause
    by_cases h : ∀ l ∈ bounds, assignment l.2 = l.1
    · exact ⟨(true,indicator),by simp,heq.mpr h⟩
    · push Not at h
      obtain ⟨l,hl,hfalse⟩ := h
      refine ⟨flip l,?_,?_⟩
      · apply List.mem_append_right
        exact List.mem_map.mpr ⟨l,hl,rfl⟩
      · have hflip := holds_negate assignment (Signal.literal l)
        exact (show assignment (flip l).2 = (flip l).1 ↔ ¬assignment l.2 = l.1 from hflip).mpr hfalse

theorem exists_profileExact (c : Coloring) (hc : NoMonochromaticTriangle c) (v : Vertex) :
    ∃ i : Fin 35, ProfileExact c v i := by
  obtain ⟨i,hi⟩ := profileData_covers (fourColorDegreeTuple c v)
    (fourColorDegreeTuple_mem_degreeTargets61 (by decide) c hc v)
  refine ⟨i,?_⟩
  simp only [profileTuple,fourColorDegreeTuple,Prod.mk.injEq] at hi
  intro q
  fin_cases q
  · simpa [palette] using hi.1.symm
  · simpa [palette] using hi.2.1.symm
  · simpa [palette] using hi.2.2.1.symm
  · simpa [palette] using hi.2.2.2.symm

def vertexProfileClauses (v : Vertex) : CNF :=
  ((List.finRange 35).flatMap fun i => conjunctionClauses (profileVar v i) (profileBounds v i)) ++
    [(List.finRange 35).map fun i => (true,profileVar v i)]

def profileClauses : CNF := (List.finRange 61).flatMap vertexProfileClauses

theorem baseValuation_profileClauses (c : Coloring) (hc : NoMonochromaticTriangle c) :
    FormulaSat (baseValuation c) profileClauses := by
  intro clause hclause
  obtain ⟨v,hv,hclause⟩ := List.mem_flatMap.mp hclause
  have hs : FormulaSat (baseValuation c) (vertexProfileClauses v) := by
    rw [vertexProfileClauses,formulaSat_append]
    constructor
    · intro clause hi
      obtain ⟨i,himem,hi⟩ := List.mem_flatMap.mp hi
      apply conjunctionClauses_sat _ _ _ ?_ clause hi
      rw [baseValuation_profile,decide_eq_true_eq]
      exact (profileBounds_all_iff c v i).symm
    · intro clause hi
      simp only [List.mem_singleton] at hi
      subst clause
      obtain ⟨i,hi⟩ := exists_profileExact c hc v
      refine ⟨(true,profileVar v i),List.mem_map.mpr ⟨i,by simp,rfl⟩,?_⟩
      simp [baseValuation_profile,hi]
  exact hs clause hclause

theorem profileExact_mass (c : Coloring) (v : Vertex) (i : Fin 35) (h : ProfileExact c v i) :
    W c v = familyMass (profileData i).1 := by
  have h0 : colorDegree c (false,false) v = (profileData i).2 0 := by simpa [palette] using h 0
  have h1 : colorDegree c (false,true) v = (profileData i).2 1 := by simpa [palette] using h 1
  have h2 : colorDegree c (true,false) v = (profileData i).2 2 := by simpa [palette] using h 2
  have h3 : colorDegree c (true,true) v = (profileData i).2 3 := by simpa [palette] using h 3
  rw [W_eq_mass4,h0,h1,h2,h3,profileData_mass]

def selectorCut : Family → Option Nat
  | .A => some 48 | .B => some 47 | .D => some 46 | _ => none

def selectorClause (v : Vertex) (i : Fin 35) : Option (List Literal) :=
  (selectorCut (profileData i).1).map fun cut =>
    [(false,profileVar v i),(false,denseAtom (hStart v) 48 59 (cut-1))]

def selectorClauses : CNF :=
  (List.finRange 61).flatMap fun v => (List.finRange 35).filterMap (selectorClause v)

theorem selector_pair_sat (c : Coloring) (v : Vertex) (i : Fin 35) (cut : Nat)
    (hpos : 0 < cut) (hcut : cut ≤ 48)
    (hexclude : ProfileExact c v i → H c v < cut) :
    ClauseSat (baseValuation c)
      [(false,profileVar v i),(false,denseAtom (hStart v) 48 59 (cut-1))] := by
  classical
  by_cases h : ProfileExact c v i
  · refine ⟨(false,denseAtom (hStart v) 48 59 (cut-1)),by simp,?_⟩
    rw [baseValuation_H_terminal c v _ (by omega)]
    have hx := hexclude h
    simp [show cut-1+1=cut by omega,show ¬cut≤H c v by omega]
  · refine ⟨(false,profileVar v i),by simp,?_⟩
    simp [baseValuation_profile,h]

theorem baseValuation_selectorClauses (c : Coloring) (selectors : SelectorX c) :
    FormulaSat (baseValuation c) selectorClauses := by
  intro clause hclause
  obtain ⟨v,hv,hclause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨i,hi,heq⟩ := List.mem_filterMap.mp hclause
  cases hfamily : (profileData i).1 <;> simp [selectorClause,selectorCut,hfamily] at heq
  case A =>
    subst clause
    apply selector_pair_sat c v i 48 (by decide) (by decide)
    intro hp
    have hm := profileExact_mass c v i hp
    simp [hfamily,familyMass] at hm
    have hs := (selectors v).1 hm
    omega
  case B =>
    subst clause
    apply selector_pair_sat c v i 47 (by decide) (by decide)
    intro hp
    have hm := profileExact_mass c v i hp
    simp [hfamily,familyMass] at hm
    have hs := (selectors v).2.1 hm
    omega
  case D =>
    subst clause
    apply selector_pair_sat c v i 46 (by decide) (by decide)
    intro hp
    have hm := profileExact_mass c v i hp
    simp [hfamily,familyMass] at hm
    have hs := (selectors v).2.2 hm
    omega

/-- Genuine normalization premises for the shared base, supplied later by
the physical-cover theorem; no opposite-high or small-fiber restriction. -/
def RootConditions (c : Coloring) : Prop :=
  (∀ q u, u ∈ rootBlocks q → c 0 u = palette q) ∧ 32 ≤ H c 0

def rootClauses : CNF :=
  ((List.finRange 4).flatMap fun q => (rootBlocks q).map fun u => [(true,edgeVar 0 u q)]) ++
    [[(true,denseAtom (hStart 0) 48 59 31)]]

theorem baseValuation_rootClauses (c : Coloring) (hroot : RootConditions c) :
    FormulaSat (baseValuation c) rootClauses := by
  rw [rootClauses,formulaSat_append]
  constructor
  · intro clause hclause
    obtain ⟨q,hq,hclause⟩ := List.mem_flatMap.mp hclause
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hclause
    have hne := rootBlocks_no_root q u hu
    refine ⟨(true,edgeVar 0 u q),by simp,?_⟩
    rw [baseValuation_physical c _ (edgeVar_bounds 0 u q hne).2]
    exact (physicalValuation_edge c 0 u q hne).mpr (hroot.1 q u hu)
  · intro clause hclause
    simp only [List.mem_singleton] at hclause
    subst clause
    refine ⟨(true,denseAtom (hStart 0) 48 59 31),by simp,?_⟩
    rw [baseValuation_H_terminal c 0 31 (by decide)]
    simp [hroot.2]

/-- The ten retained deterministic families, exactly in the frozen producer
order. The discarded33guard clauses do not occur in this formula. -/
def broaderBaseCNF : CNF :=
  coreCNF ++ highnessClauses ++ HClauses ++ profileClauses ++ selectorClauses ++ rootClauses ++ fiberClauses

theorem coloring_satisfies_broaderBase (c : Coloring) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (hroot : RootConditions c) :
    FormulaSat (baseValuation c) broaderBaseCNF := by
  simp only [broaderBaseCNF,formulaSat_append]
  exact ⟨⟨⟨⟨⟨⟨baseValuation_coreCNF c hc,baseValuation_highnessClauses c⟩,
    baseValuation_HClauses c⟩,baseValuation_profileClauses c hc⟩,
    baseValuation_selectorClauses c selectors⟩,baseValuation_rootClauses c hroot⟩,
    baseValuation_fiberClauses c⟩

theorem broaderBase_satisfiable_of_normalized_host (c : Coloring) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (hroot : RootConditions c) :
    ∃ assignment : Nat → Bool,
      ∀ clause ∈ broaderBaseCNF, ∃ literal ∈ clause, assignment literal.2 = literal.1 := by
  exact ⟨baseValuation c,coloring_satisfies_broaderBase c hc selectors hroot⟩

#print axioms Ramsey61.CEncodingBase.baseValuation_HClauses
#print axioms Ramsey61.CEncodingBase.baseValuation_profileClauses
#print axioms Ramsey61.CEncodingBase.baseValuation_selectorClauses
#print axioms Ramsey61.CEncodingBase.coloring_satisfies_broaderBase
#print axioms Ramsey61.CEncodingBase.broaderBase_satisfiable_of_normalized_host
end Ramsey61.CEncodingBase
