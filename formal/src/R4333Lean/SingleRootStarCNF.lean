import R4333Lean.CriticalTemplatePaletteSymmetry
import R4333Lean.FiniteColorCNF

/-!
# Exact canonical single-root star CNF

This file mirrors the uncapped, canonical-palette mode of
`r4333_upper/single_root_star_pilot.py`.  The non-root vertices are
`0,...,59`.  DIMACS-style edge variables are exactly `1,...,7080`, in
lexicographic edge order and then colour order.  Template selectors start at
7081 and are allocated in block order, with the twisted selector first.

No unsatisfiability assertion is made here.  The main result is the sound
direction needed at the LRAT boundary: a normalized semantic star witness
gives a valuation satisfying the generated formula.  The premise called
`templateCanonical` is the exact remaining obligation of the semantic
front-end.  `CriticalTemplatePaletteSymmetry.lean` proves that independently
relabeling the vertices of each critical block can arrange this canonical
palette without restricting its cross-block edges.
-/

namespace R4333

open FiniteColorCNF

namespace SingleRootStarCNF

inductive Profile where
  | p12_16_16_16
  | p13_15_16_16
  | p14_14_16_16
  | p14_15_15_16
  deriving DecidableEq, Fintype, Repr

def profileSizes : Profile → List Nat
  | .p12_16_16_16 => [12, 16, 16, 16]
  | .p13_15_16_16 => [13, 15, 16, 16]
  | .p14_14_16_16 => [14, 14, 16, 16]
  | .p14_15_15_16 => [14, 15, 15, 16]

def blockSize (profile : Profile) (block : Nat) : Nat :=
  (profileSizes profile).getD block 0

def blockStart (profile : Profile) (block : Nat) : Nat :=
  ((profileSizes profile).take block).sum

def isCriticalBlock (profile : Profile) (block : Nat) : Prop :=
  blockSize profile block = 15 ∨ blockSize profile block = 16

instance (profile : Profile) (block : Nat) :
    Decidable (isCriticalBlock profile block) := by
  unfold isCriticalBlock
  infer_instance

/-- Rank among earlier critical blocks.  This is precisely the selector
allocation order of the Python producer. -/
def criticalBlockRank (profile : Profile) (block : Nat) : Nat :=
  match profile with
  | .p12_16_16_16 => block - 1
  | .p13_15_16_16 => block - 1
  | .p14_14_16_16 => block - 2
  | .p14_15_15_16 => block - 1

/-- Zero-based rank of an unordered edge in the canonical list on 60
vertices. -/
def edgeRank (left right : Nat) : Nat :=
  (FiniteColorCNF.edges 60).idxOf (min left right, max left right)

/-- Exact DIMACS variable allocated by `IDPool` for a non-root edge. -/
def edgeAtom (left right color : Nat) : Nat :=
  1 + 4 * edgeRank left right + color

/-- Exact DIMACS selector variable.  Python emits `T` before `U`, so
`twisted = true` has offset zero. -/
def selectorAtom (profile : Profile) (block : Nat) (twisted : Bool) : Nat :=
  7081 + 2 * criticalBlockRank profile block + if twisted then 0 else 1

def canonicalPalette : Fin 4 → Fin 3 → Fin 4 := ![
  ![1, 2, 3],
  ![0, 2, 3],
  ![0, 1, 3],
  ![0, 1, 2]
]

def fin15 (x : Nat) : Fin 15 :=
  ⟨x % 15, Nat.mod_lt _ (by decide)⟩

def fin16 (x : Nat) : Fin 16 :=
  ⟨x % 16, Nat.mod_lt _ (by decide)⟩

/-- The abstract template colour used by the producer.  The `size = 15`
branch is the only non-16 branch that occurs in a critical block. -/
def templateColor (size : Nat) (twisted : Bool)
    (left right : Nat) : Fin 3 :=
  if size = 15 then
    k15Template twisted (fin15 left) (fin15 right)
  else
    k16Template twisted (fin16 left) (fin16 right)

def blockVertex (profile : Profile) (block position : Nat) : Fin 60 :=
  ⟨(blockStart profile block + position) % 60,
    Nat.mod_lt _ (by decide)⟩

/-! ## Clause generator -/

def exactlyOneClauses (atoms : List Nat) : Sat.Fmla :=
  [atoms.map Sat.Literal.pos] ++
    (FiniteColorCNF.edges atoms.length).map fun pair =>
      [Sat.Literal.neg (atoms.getD pair.1 0),
       Sat.Literal.neg (atoms.getD pair.2 0)]

def edgeExactlyOneClauses : Sat.Fmla :=
  (FiniteColorCNF.edges 60).flatMap fun pair =>
    exactlyOneClauses ((List.range 4).map fun q =>
      edgeAtom pair.1 pair.2 q)

def rootTriangleUnitClauses (profile : Profile) : Sat.Fmla :=
  (List.range 4).flatMap fun block =>
    (FiniteColorCNF.edges (blockSize profile block)).map fun pair =>
      [Sat.Literal.neg (edgeAtom
        (blockStart profile block + pair.1)
        (blockStart profile block + pair.2) block)]

def templateGuardClauses (profile : Profile) (block : Nat)
    (twisted : Bool) : Sat.Fmla :=
  let size := blockSize profile block
  (FiniteColorCNF.edges size).map fun pair =>
    [Sat.Literal.neg (selectorAtom profile block twisted),
     Sat.Literal.pos (edgeAtom
       (blockStart profile block + pair.1)
       (blockStart profile block + pair.2)
       (canonicalPalette ⟨block % 4, Nat.mod_lt _ (by decide)⟩
         (templateColor size twisted pair.1 pair.2)).val)]

def criticalBlockClauses (profile : Profile) (block : Nat) : Sat.Fmla :=
  if isCriticalBlock profile block then
    templateGuardClauses profile block true ++
    templateGuardClauses profile block false ++
    exactlyOneClauses
      [selectorAtom profile block true, selectorAtom profile block false]
  else []

def allCriticalBlockClauses (profile : Profile) : Sat.Fmla :=
  (List.range 4).flatMap (criticalBlockClauses profile)

def nonrootTriangleClauses : Sat.Fmla :=
  (FiniteColorCNF.triples 60).flatMap fun triple =>
    (List.range 4).map fun color =>
      [Sat.Literal.neg (edgeAtom triple.1 triple.2.1 color),
       Sat.Literal.neg (edgeAtom triple.1 triple.2.2 color),
       Sat.Literal.neg (edgeAtom triple.2.1 triple.2.2 color)]

/-- The exact uncapped canonical single-root formula, in producer clause
order. -/
def fmla (profile : Profile) : Sat.Fmla :=
  edgeExactlyOneClauses ++
  rootTriangleUnitClauses profile ++
  allCriticalBlockClauses profile ++
  nonrootTriangleClauses

/-! ## Semantic normalized witness and its valuation -/

structure CanonicalStarWitness (profile : Profile) where
  coloring : EdgeColoring (Fin 60) (Fin 4)
  noMono : NoMonochromaticTriangle coloring
  chosenTemplate : Fin 4 → Bool
  rootForbidden : ∀ (block : Fin 4) (left right : Nat),
    left < blockSize profile block →
    right < blockSize profile block → left < right →
    coloring (blockVertex profile block left)
      (blockVertex profile block right) ≠ block
  templateCanonical : ∀ (block : Fin 4),
    isCriticalBlock profile block →
    ∀ (left right : Nat),
      left < blockSize profile block →
      right < blockSize profile block → left < right →
      coloring (blockVertex profile block left)
          (blockVertex profile block right) =
        canonicalPalette block
          (templateColor (blockSize profile block)
            (chosenTemplate block) left right)

/-- A direct valuation of the exact compact DIMACS namespace.  The first
disjunct decodes edge variables extensionally; the second selects exactly
one template atom in every critical block. -/
def witnessValuation {profile : Profile}
    (w : CanonicalStarWitness profile) : Sat.Valuation := fun atom =>
  if atom ≤ 7080 then
    ∃ left right : Fin 60, ∃ color : Fin 4,
      left < right ∧ atom = edgeAtom left right color ∧
        w.coloring left right = color
  else
    ∃ block : Fin 4, isCriticalBlock profile block ∧
      atom = selectorAtom profile block (w.chosenTemplate block)

/-! ## Exact atom evaluation -/

theorem mem_edges_bounds {n left right : Nat}
    (h : (left, right) ∈ FiniteColorCNF.edges n) :
    left < n ∧ right < n ∧ left < right := by
  simp only [FiniteColorCNF.edges, FiniteColorCNF.vertices,
    List.mem_flatMap, List.mem_map] at h
  obtain ⟨left', hleft, right', hright, hp⟩ := h
  have hleft' : left' < n := by simpa using hleft
  have hrightMem : right' ∈ List.range n := (List.mem_filter.mp hright).1
  have hright' : right' < n := by simpa using hrightMem
  have hlr : left' < right' :=
    of_decide_eq_true (List.mem_filter.mp hright).2
  injection hp with hleq hreq
  subst left'
  subst right'
  exact ⟨hleft', hright', hlr⟩

theorem blockStart_add_lt_sixty (profile : Profile) (block : Fin 4)
    {position : Nat} (hposition : position < blockSize profile block) :
    blockStart profile block + position < 60 := by
  cases profile <;> fin_cases block <;>
    simp [blockSize, blockStart, profileSizes] at hposition ⊢ <;> omega

@[simp] theorem blockVertex_val (profile : Profile) (block : Fin 4)
    {position : Nat} (hposition : position < blockSize profile block) :
    (blockVertex profile block position).val =
      blockStart profile block + position := by
  simp [blockVertex, Nat.mod_eq_of_lt
    (blockStart_add_lt_sixty profile block hposition)]

theorem edgeAtom_injective_of_ordered
    {left right left' right' color color' : Nat}
    (hleft : left < 60) (hright : right < 60) (hlr : left < right)
    (hleft' : left' < 60) (hright' : right' < 60)
    (hlr' : left' < right') (hcolor : color < 4)
    (hcolor' : color' < 4)
    (hatom : edgeAtom left right color = edgeAtom left' right' color') :
    left = left' ∧ right = right' ∧ color = color' := by
  have hedge : (left, right) ∈ FiniteColorCNF.edges 60 :=
    FiniteColorCNF.mem_edges_of_bounds hleft hright hlr
  have hedge' : (left', right') ∈ FiniteColorCNF.edges 60 :=
    FiniteColorCNF.mem_edges_of_bounds hleft' hright' hlr'
  have hmin : min left right = left := min_eq_left (Nat.le_of_lt hlr)
  have hmax : max left right = right := max_eq_right (Nat.le_of_lt hlr)
  have hmin' : min left' right' = left' := min_eq_left (Nat.le_of_lt hlr')
  have hmax' : max left' right' = right' := max_eq_right (Nat.le_of_lt hlr')
  simp only [edgeAtom, edgeRank, hmin, hmax, hmin', hmax'] at hatom
  have hrank :
      (FiniteColorCNF.edges 60).idxOf (left, right) =
        (FiniteColorCNF.edges 60).idxOf (left', right') := by
    omega
  have hq : color = color' := by omega
  have hpairs : (left, right) = (left', right') :=
    (List.idxOf_inj hedge).mp hrank
  exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs, hq⟩

set_option maxRecDepth 100000 in
theorem edges60_length : (FiniteColorCNF.edges 60).length = 1770 := by
  decide

theorem edgeAtom_le_7080 (left right : Fin 60) (color : Fin 4)
    (hlr : left < right) : edgeAtom left right color ≤ 7080 := by
  have hedge : (left.val, right.val) ∈ FiniteColorCNF.edges 60 :=
    FiniteColorCNF.mem_edges_of_bounds left.isLt right.isLt hlr
  have hrank : edgeRank left right < (FiniteColorCNF.edges 60).length := by
    simpa [edgeRank, min_eq_left (Nat.le_of_lt hlr),
      max_eq_right (Nat.le_of_lt hlr)] using List.idxOf_lt_length_of_mem hedge
  rw [edges60_length] at hrank
  unfold edgeAtom
  omega

theorem witnessValuation_edgeAtom_iff {profile : Profile}
    (w : CanonicalStarWitness profile) (left right : Fin 60)
    (color : Fin 4) (hlr : left < right) :
    witnessValuation w (edgeAtom left right color) ↔
      w.coloring left right = color := by
  rw [witnessValuation, if_pos (edgeAtom_le_7080 left right color hlr)]
  constructor
  · rintro ⟨left', right', color', hlr', hatom, hcolor'⟩
    obtain ⟨hleft, hright, hcolor⟩ := edgeAtom_injective_of_ordered
      left'.isLt right'.isLt hlr' left.isLt right.isLt hlr
      color'.isLt color.isLt hatom.symm
    have hleftFin : left' = left := Fin.ext hleft
    have hrightFin : right' = right := Fin.ext hright
    have hcolorFin : color' = color := Fin.ext hcolor
    subst left'
    subst right'
    subst color'
    exact hcolor'
  · intro hcolor
    exact ⟨left, right, color, hlr, rfl, hcolor⟩

theorem selectorAtom_gt_7080 (profile : Profile) (block : Fin 4)
    (twisted : Bool) (_hcritical : isCriticalBlock profile block) :
    7080 < selectorAtom profile block twisted := by
  unfold selectorAtom
  omega

theorem selectorAtom_injective_on_critical :
    ∀ (profile : Profile) (left right : Fin 4) (a b : Bool),
      isCriticalBlock profile left → isCriticalBlock profile right →
      selectorAtom profile left a = selectorAtom profile right b →
      left = right ∧ a = b := by
  intro profile left right a b hleft hright hatom
  cases profile <;> fin_cases left <;> fin_cases right <;>
    cases a <;> cases b <;>
    simp [isCriticalBlock, blockSize, profileSizes, selectorAtom,
      criticalBlockRank] at hleft hright hatom ⊢

theorem witnessValuation_selectorAtom_iff {profile : Profile}
    (w : CanonicalStarWitness profile) (block : Fin 4) (twisted : Bool)
    (hcritical : isCriticalBlock profile block) :
    witnessValuation w (selectorAtom profile block twisted) ↔
      w.chosenTemplate block = twisted := by
  rw [witnessValuation,
    if_neg (Nat.not_le_of_lt
      (selectorAtom_gt_7080 profile block twisted hcritical))]
  constructor
  · rintro ⟨other, hother, hatom⟩
    obtain ⟨hblock, htwisted⟩ := selectorAtom_injective_on_critical
      profile other block (w.chosenTemplate other) twisted
      hother hcritical hatom.symm
    subst other
    exact htwisted
  · intro htwisted
    exact ⟨block, hcritical, by rw [htwisted]⟩

/-! ## Satisfaction of the four clause layers -/

theorem satisfies_exactlyOneClauses_of_unique
    (valuation : Sat.Valuation) (atoms : List Nat)
    (hsome : ∃ atom, atom ∈ atoms ∧ valuation atom)
    (hunique : ∀ i j,
      i < atoms.length → j < atoms.length → i < j →
      ¬(valuation (atoms.getD i 0) ∧ valuation (atoms.getD j 0))) :
    valuation.satisfies_fmla (exactlyOneClauses atoms) := by
  constructor
  intro clause hclause
  change List.Mem clause
    ((show Sat.Clause from atoms.map Sat.Literal.pos) ::
      (FiniteColorCNF.edges atoms.length).map fun pair =>
        [Sat.Literal.neg (atoms.getD pair.1 0),
         Sat.Literal.neg (atoms.getD pair.2 0)]) at hclause
  cases hclause with
  | head =>
    obtain ⟨atom, hatom, htrue⟩ := hsome
    apply FiniteColorCNF.satisfies_of_mem_holds valuation
      (l := Sat.Literal.pos atom)
    · exact List.mem_map.mpr ⟨atom, hatom, rfl⟩
    · exact htrue
  | tail ignored hnegative =>
    obtain ⟨pair, hpair, hp⟩ := (List.mem_map).mp hnegative
    subst clause
    obtain ⟨hi, hj, hij⟩ := mem_edges_bounds hpair
    by_cases hvi : valuation (atoms.getD pair.1 0)
    · apply FiniteColorCNF.satisfies_of_mem_holds valuation
        (l := Sat.Literal.neg (atoms.getD pair.2 0))
        (List.Mem.tail _ (List.Mem.head _))
      intro hvj
      exact hunique pair.1 pair.2 hi hj hij ⟨hvi, hvj⟩
    · apply FiniteColorCNF.satisfies_of_mem_holds valuation
        (l := Sat.Literal.neg (atoms.getD pair.1 0))
        (List.Mem.head _)
      exact hvi

theorem rangeMap_getD {k : Nat} (f : Nat → Nat) {q : Nat}
    (hq : q < k) :
    ((List.range k).map f).getD q (f 0) = f q := by
  simp [List.getD, hq]

theorem witnessValuation_satisfies_edgeExactlyOneClauses
    {profile : Profile} (w : CanonicalStarWitness profile) :
    (witnessValuation w).satisfies_fmla edgeExactlyOneClauses := by
  constructor
  intro clause hclause
  simp only [edgeExactlyOneClauses, List.mem_flatMap] at hclause
  obtain ⟨pair, hpair, hclause⟩ := hclause
  obtain ⟨hleft, hright, hlr⟩ := mem_edges_bounds hpair
  let left : Fin 60 := ⟨pair.1, hleft⟩
  let right : Fin 60 := ⟨pair.2, hright⟩
  let actual : Fin 4 := w.coloring left right
  have hsatisfies := satisfies_exactlyOneClauses_of_unique
    (witnessValuation w)
    ((List.range 4).map fun q => edgeAtom pair.1 pair.2 q)
    (by
      refine ⟨edgeAtom pair.1 pair.2 actual, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨actual, List.mem_range.mpr actual.isLt, rfl⟩
      · exact (witnessValuation_edgeAtom_iff w left right actual hlr).2 rfl)
    (by
      intro i j hi hj hij hboth
      have hgeti :
          ((List.range 4).map fun q => edgeAtom pair.1 pair.2 q).getD i 0 =
            edgeAtom pair.1 pair.2 i := by
        have hi4 : i < 4 := by simpa using hi
        simp [List.getD, List.getElem?_range hi4]
      have hgetj :
          ((List.range 4).map fun q => edgeAtom pair.1 pair.2 q).getD j 0 =
            edgeAtom pair.1 pair.2 j := by
        have hj4 : j < 4 := by simpa using hj
        simp [List.getD, List.getElem?_range hj4]
      rw [hgeti, hgetj] at hboth
      let qi : Fin 4 := ⟨i, by simpa using hi⟩
      let qj : Fin 4 := ⟨j, by simpa using hj⟩
      have hci := (witnessValuation_edgeAtom_iff w left right qi hlr).1 hboth.1
      have hcj := (witnessValuation_edgeAtom_iff w left right qj hlr).1 hboth.2
      have : qi = qj := hci.symm.trans hcj
      exact (Nat.ne_of_lt hij) (congrArg Fin.val this))
  exact hsatisfies.prop clause hclause

theorem witnessValuation_satisfies_rootTriangleUnitClauses
    {profile : Profile} (w : CanonicalStarWitness profile) :
    (witnessValuation w).satisfies_fmla
      (rootTriangleUnitClauses profile) := by
  constructor
  intro clause hclause
  simp only [rootTriangleUnitClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨block, hblock, pair, hpair, rfl⟩ := hclause
  have hblockLt : block < 4 := List.mem_range.mp hblock
  let block' : Fin 4 := ⟨block, hblockLt⟩
  obtain ⟨hleft, hright, hlr⟩ := mem_edges_bounds hpair
  have hleftAbs := blockStart_add_lt_sixty profile block' hleft
  have hrightAbs := blockStart_add_lt_sixty profile block' hright
  let left : Fin 60 := ⟨blockStart profile block + pair.1, hleftAbs⟩
  let right : Fin 60 := ⟨blockStart profile block + pair.2, hrightAbs⟩
  have hlrAbs : left < right := by simp [left, right]; omega
  apply FiniteColorCNF.satisfies_of_mem_holds (witnessValuation w)
    (l := Sat.Literal.neg (edgeAtom left right block')) (List.Mem.head _)
  rw [Holds]
  rw [witnessValuation_edgeAtom_iff w left right block' hlrAbs]
  have hleftVertex : blockVertex profile block' pair.1 = left := by
    apply Fin.ext
    simpa [left] using blockVertex_val profile block' hleft
  have hrightVertex : blockVertex profile block' pair.2 = right := by
    apply Fin.ext
    simpa [right] using blockVertex_val profile block' hright
  simpa [hleftVertex, hrightVertex] using
    w.rootForbidden block' pair.1 pair.2 hleft hright hlr

@[simp] theorem fin4_mod_val (block : Fin 4) :
    (⟨block.val % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = block := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt block.isLt

theorem witnessValuation_satisfies_templateGuardClauses
    {profile : Profile} (w : CanonicalStarWitness profile)
    (block : Fin 4) (twisted : Bool)
    (hcritical : isCriticalBlock profile block) :
    (witnessValuation w).satisfies_fmla
      (templateGuardClauses profile block twisted) := by
  constructor
  intro clause hclause
  simp only [templateGuardClauses, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  obtain ⟨hleft, hright, hlr⟩ := mem_edges_bounds hpair
  have hleftAbs := blockStart_add_lt_sixty profile block hleft
  have hrightAbs := blockStart_add_lt_sixty profile block hright
  let left : Fin 60 :=
    ⟨blockStart profile block + pair.1, hleftAbs⟩
  let right : Fin 60 :=
    ⟨blockStart profile block + pair.2, hrightAbs⟩
  have hlrAbs : left < right := by simp [left, right]; omega
  by_cases hchoice : w.chosenTemplate block = twisted
  · let actual : Fin 4 := canonicalPalette block
      (templateColor (blockSize profile block) twisted pair.1 pair.2)
    apply FiniteColorCNF.satisfies_of_mem_holds (witnessValuation w)
      (l := Sat.Literal.pos (edgeAtom
        (blockStart profile block + pair.1)
        (blockStart profile block + pair.2)
        (canonicalPalette
          ⟨block.val % 4, Nat.mod_lt _ (by decide)⟩
          (templateColor (blockSize profile block) twisted
            pair.1 pair.2)).val))
      (List.Mem.tail _ (List.Mem.head _))
    rw [Holds]
    have hatom : edgeAtom
        (blockStart profile block + pair.1)
        (blockStart profile block + pair.2)
        (canonicalPalette
          ⟨block.val % 4, Nat.mod_lt _ (by decide)⟩
          (templateColor (blockSize profile block) twisted
            pair.1 pair.2)).val = edgeAtom left right actual := by
      simp [left, right, actual]
    rw [hatom]
    rw [witnessValuation_edgeAtom_iff w left right actual hlrAbs]
    have hleftVertex : blockVertex profile block pair.1 = left := by
      apply Fin.ext
      simpa [left] using blockVertex_val profile block hleft
    have hrightVertex : blockVertex profile block pair.2 = right := by
      apply Fin.ext
      simpa [right] using blockVertex_val profile block hright
    have htemplate := w.templateCanonical block hcritical pair.1 pair.2
      hleft hright hlr
    rw [hchoice] at htemplate
    simpa [actual, hleftVertex, hrightVertex] using htemplate
  · apply FiniteColorCNF.satisfies_of_mem_holds (witnessValuation w)
      (l := Sat.Literal.neg (selectorAtom profile block twisted))
      (List.Mem.head _)
    rw [Holds]
    rw [witnessValuation_selectorAtom_iff w block twisted hcritical]
    exact hchoice

theorem witnessValuation_satisfies_selectorExactlyOne
    {profile : Profile} (w : CanonicalStarWitness profile)
    (block : Fin 4) (hcritical : isCriticalBlock profile block) :
    (witnessValuation w).satisfies_fmla
      (exactlyOneClauses
        [selectorAtom profile block true, selectorAtom profile block false]) := by
  apply satisfies_exactlyOneClauses_of_unique
  · refine ⟨selectorAtom profile block (w.chosenTemplate block), ?_, ?_⟩
    · cases h : w.chosenTemplate block <;> simp
    · exact (witnessValuation_selectorAtom_iff w block
        (w.chosenTemplate block) hcritical).2 rfl
  · intro i j hi hj hij hboth
    have hi2 : i < 2 := by simpa using hi
    have hj2 : j < 2 := by simpa using hj
    have hiz : i = 0 := by omega
    have hjo : j = 1 := by omega
    subst i
    subst j
    simp only [List.getD] at hboth
    have ht := (witnessValuation_selectorAtom_iff w block true hcritical).1
      hboth.1
    have hf := (witnessValuation_selectorAtom_iff w block false hcritical).1
      hboth.2
    simp_all

theorem witnessValuation_satisfies_criticalBlockClauses
    {profile : Profile} (w : CanonicalStarWitness profile) (block : Fin 4) :
    (witnessValuation w).satisfies_fmla
      (criticalBlockClauses profile block) := by
  by_cases hcritical : isCriticalBlock profile block
  · rw [criticalBlockClauses, if_pos hcritical]
    constructor
    intro clause hclause
    simp only [List.mem_append] at hclause
    rcases hclause with (hclause | hclause) | hclause
    · exact (witnessValuation_satisfies_templateGuardClauses
        w block true hcritical).prop clause hclause
    · exact (witnessValuation_satisfies_templateGuardClauses
        w block false hcritical).prop clause hclause
    · exact (witnessValuation_satisfies_selectorExactlyOne
        w block hcritical).prop clause hclause
  · rw [criticalBlockClauses, if_neg hcritical]
    exact ⟨by simp⟩

theorem witnessValuation_satisfies_allCriticalBlockClauses
    {profile : Profile} (w : CanonicalStarWitness profile) :
    (witnessValuation w).satisfies_fmla
      (allCriticalBlockClauses profile) := by
  constructor
  intro clause hclause
  simp only [allCriticalBlockClauses, List.mem_flatMap] at hclause
  obtain ⟨block, hblock, hclause⟩ := hclause
  let block' : Fin 4 := ⟨block, List.mem_range.mp hblock⟩
  exact (witnessValuation_satisfies_criticalBlockClauses w block').prop
    clause hclause

theorem witnessValuation_satisfies_nonrootTriangleClauses
    {profile : Profile} (w : CanonicalStarWitness profile) :
    (witnessValuation w).satisfies_fmla nonrootTriangleClauses := by
  constructor
  intro clause hclause
  simp only [nonrootTriangleClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨triple, htriple, color, hcolor, rfl⟩ := hclause
  obtain ⟨hleft, hmiddle, hright, hlm, hmr⟩ :=
    FiniteColorCNF.mem_triples_iff_bounds htriple
  have hcolorLt : color < 4 := List.mem_range.mp hcolor
  let left : Fin 60 := ⟨triple.1, hleft⟩
  let middle : Fin 60 := ⟨triple.2.1, hmiddle⟩
  let right : Fin 60 := ⟨triple.2.2, hright⟩
  let q : Fin 4 := ⟨color, hcolorLt⟩
  have hlr : left < right := hlm.trans hmr
  have hdistinct : PairwiseDistinct left middle right :=
    ⟨Fin.ne_of_lt hlm, Fin.ne_of_lt hlr, Fin.ne_of_lt hmr⟩
  have hnot : ¬(w.coloring left middle = q ∧
      w.coloring left right = q ∧ w.coloring middle right = q) := by
    rintro ⟨hlmq, hlrq, hmrq⟩
    apply w.noMono left middle right hdistinct
    exact ⟨hlmq.trans hlrq.symm, hlrq.trans hmrq.symm⟩
  by_cases hlmq : w.coloring left middle = q
  · by_cases hlrq : w.coloring left right = q
    · apply FiniteColorCNF.satisfies_of_mem_holds (witnessValuation w)
          (l := Sat.Literal.neg (edgeAtom middle right q))
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      rw [Holds]
      rw [witnessValuation_edgeAtom_iff w middle right q hmr]
      intro hmrq
      exact hnot ⟨hlmq, hlrq, hmrq⟩
    · apply FiniteColorCNF.satisfies_of_mem_holds (witnessValuation w)
          (l := Sat.Literal.neg (edgeAtom left right q))
          (List.Mem.tail _ (List.Mem.head _))
      rw [Holds]
      rw [witnessValuation_edgeAtom_iff w left right q hlr]
      exact hlrq
  · apply FiniteColorCNF.satisfies_of_mem_holds (witnessValuation w)
        (l := Sat.Literal.neg (edgeAtom left middle q))
        (List.Mem.head _)
    rw [Holds]
    rw [witnessValuation_edgeAtom_iff w left middle q hlm]
    exact hlmq

/-- Every normalized semantic star witness satisfies the exact compact
formula used by the external producer. -/
theorem witnessValuation_satisfies_fmla {profile : Profile}
    (w : CanonicalStarWitness profile) :
    (witnessValuation w).satisfies_fmla (fmla profile) := by
  constructor
  intro clause hclause
  simp only [fmla, List.mem_append] at hclause
  rcases hclause with ((hclause | hclause) | hclause) | hclause
  · exact (witnessValuation_satisfies_edgeExactlyOneClauses w).prop
      clause hclause
  · exact (witnessValuation_satisfies_rootTriangleUnitClauses w).prop
      clause hclause
  · exact (witnessValuation_satisfies_allCriticalBlockClauses w).prop
      clause hclause
  · exact (witnessValuation_satisfies_nonrootTriangleClauses w).prop
      clause hclause

theorem exists_satisfyingValuation_of_witness {profile : Profile}
    (w : CanonicalStarWitness profile) :
    ∃ valuation : Sat.Valuation,
      valuation.satisfies_fmla (fmla profile) :=
  ⟨witnessValuation w, witnessValuation_satisfies_fmla w⟩

/-- Checked LRAT over this exact formula rules out the corresponding
normalized star branch.  This theorem asserts no such refutation. -/
theorem noCanonicalStarWitness_of_lrat {profile : Profile}
    (hunsat : (fmla profile).proof Sat.Clause.nil) :
    ¬Nonempty (CanonicalStarWitness profile) := by
  rintro ⟨w⟩
  exact hunsat (witnessValuation w) (witnessValuation_satisfies_fmla w)

#print axioms R4333.SingleRootStarCNF.witnessValuation_satisfies_fmla
#print axioms R4333.SingleRootStarCNF.exists_satisfyingValuation_of_witness
#print axioms R4333.SingleRootStarCNF.noCanonicalStarWitness_of_lrat

end SingleRootStarCNF

end R4333
