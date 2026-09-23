import R4333Lean.ProfileDUUUFourSupportP0SelectorCNF61

/-!
# Semantic valuation bridge for the four-support selector formula

An `ExactRepresentativeBranch` is the semantic object promised by the
support and restored-`K15` orbit layers: a normalized block-zero/position-zero
four-support branch, one of the three support pairs, and one of the 36 exact
matrix representatives.  This file constructs the exact valuation of the
authoritative selector formula and proves satisfaction.

There is no refutation premise or LRAT import in this module.
-/

namespace R4333
namespace ProfileDUUUFourSupportP0SelectorBridge61

open ColoringJoinRows
open FiniteColorCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourSupportInside61
open ProfileDFourSupportForeignSupports61
open ProfileDUUUFourSupportPositionSymmetry61
open ProfileDUUUFourSupportP0SupportPair61
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUFourSupportP0RepresentativeData61
open ProfileDUUUFourSupportP0SelectorCNF61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## Restrict the five-row semantic object to the first four rows -/

def fourExtension (branch : Branch) :
    ProfileDFourRowBoundary.FourExtension .uuu where
  tail := branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  inside := firstFourInsideColoring (semantic branch)
  rows := fun row =>
    branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row.castSucc
  insideNoMono := firstFourInsideColoring_noMono (semantic branch)
  insideRootForbidden := by
    intro left right hne
    exact firstFourInsideColoring_ne_zero (semantic branch) left right hne
  rowsAdmissible := by
    intro row
    exact branch.toDegreeFlooredFiveExtension.toFiveExtension.rowsAdmissible
      row.castSucc
  rowsPairCompatible := by
    intro left right hne x hbad
    exact branch.toDegreeFlooredFiveExtension.toFiveExtension.rowsPairCompatible
      left.castSucc right.castSucc (Fin.castSuccEmb.injective.ne hne) x hbad

/-! ## Exact semantic leaf supplied by the matrix quotient -/

structure ExactRepresentativeBranch where
  pair : SupportPair
  selector : MatrixSelector
  selectorPair : matrixPair selector = pair
  branch : Branch
  firstSupportExact : ∀ p : Fin 15,
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDTripleJoinReduction.blockVertex 0 0)
        (ProfileDTripleJoinReduction.blockVertex 1 p.val) = 1 ↔
      p ∈ pairFirstSupport pair
  secondSupportExact : ∀ p : Fin 16,
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDTripleJoinReduction.blockVertex 0 0)
        (ProfileDTripleJoinReduction.blockVertex 2 p.val) = 1 ↔
      p ∈ pairSecondSupport pair
  matrixExact : ∀ left right : Fin 14, left ≠ right →
    ProfileDFourRowCNF.totalColoring (fourExtension branch)
        (physicalVertex (pairSupportKind pair) left)
        (physicalVertex (pairSupportKind pair) right) =
      representativeMatrixColor selector left right

def baseValuation (exact : ExactRepresentativeBranch) : Sat.Valuation :=
  coloringValuation
    (ProfileDFourRowCNF.totalColoring (fourExtension exact.branch))

/-! ## Sparse selector valuation -/

noncomputable def selectorValuation
    (exact : ExactRepresentativeBranch) : Sat.Valuation := fun atom =>
  if atom < firstSelectorAtom then
    baseValuation exact atom
  else
    atom = pairSelectorAtom exact.pair ∨
      atom = matrixSelectorAtom exact.selector

theorem selectorValuation_eq_below
    (exact : ExactRepresentativeBranch) (atom : Nat)
    (hbelow : atom < firstSelectorAtom) :
    selectorValuation exact atom ↔ baseValuation exact atom := by
  simp [selectorValuation, hbelow]

@[simp] theorem selectorValuation_pairSelector
    (exact : ExactRepresentativeBranch) (pair : SupportPair) :
    selectorValuation exact (pairSelectorAtom pair) ↔
      pair = exact.pair := by
  simp only [selectorValuation, pairSelectorAtom, firstSelectorAtom]
  have hnotBelow : ¬6000054 + pair.val < 6000054 := by omega
  rw [if_neg hnotBelow]
  constructor
  · rintro (hpair | hmatrix)
    · apply Fin.ext
      omega
    · exfalso
      unfold matrixSelectorAtom at hmatrix
      simp [firstSelectorAtom] at hmatrix
      omega
  · intro hpair
    left
    subst pair
    rfl

@[simp] theorem selectorValuation_matrixSelector
    (exact : ExactRepresentativeBranch) (selector : MatrixSelector) :
    selectorValuation exact (matrixSelectorAtom selector) ↔
      selector = exact.selector := by
  simp only [selectorValuation, matrixSelectorAtom, firstSelectorAtom]
  have hnotBelow : ¬6000054 + 3 + selector.val < 6000054 := by omega
  rw [if_neg hnotBelow]
  constructor
  · rintro (hpair | hselector)
    · exfalso
      unfold pairSelectorAtom at hpair
      simp [firstSelectorAtom] at hpair
      omega
    · apply Fin.ext
      omega
  · intro hselector
    right
    subst selector
    rfl

/-! ## Ordinary edge atoms lie below the selector interval -/

theorem orderedEdgeAtom_lt_firstSelector
    (left right : ProfileDFourRowCNF.TotalVertex) (color : Fin 4)
    (hlr : left.val < right.val) :
    edgeAtom left.val right.val color.val < firstSelectorAtom := by
  have hright : right.val ≤ 49 := by omega
  have hleft : left.val ≤ 48 := by omega
  have hcolor : color.val ≤ 3 := by omega
  have hrightSq : right.val * right.val ≤ 49 * 49 :=
    Nat.mul_le_mul hright hright
  have hinner : right.val * right.val + left.val ≤ 2449 := by omega
  by_cases houter : right.val * right.val + left.val < color.val
  · have hcolorSq : color.val * color.val ≤ 3 * 3 :=
      Nat.mul_le_mul hcolor hcolor
    simp [edgeAtom, Nat.pair, hlr, houter, firstSelectorAtom]
    omega
  · have hinnerSq :
        (right.val * right.val + left.val) *
            (right.val * right.val + left.val) ≤
          2449 * 2449 := Nat.mul_le_mul hinner hinner
    simp [edgeAtom, Nat.pair, hlr, houter, firstSelectorAtom]
    omega

theorem selectorValuation_orderedEdgeAtom
    (exact : ExactRepresentativeBranch)
    (left right : ProfileDFourRowCNF.TotalVertex) (color : Fin 4)
    (hlr : left.val < right.val) :
    selectorValuation exact (edgeAtom left.val right.val color.val) ↔
      ProfileDFourRowCNF.totalColoring (fourExtension exact.branch)
        left right = color := by
  rw [selectorValuation_eq_below exact _
    (orderedEdgeAtom_lt_firstSelector left right color hlr)]
  exact coloringValuation_edgeAtom _ left right color

/-! ## The exact base formula survives the selector override -/

def literalAtom : Sat.Literal → Nat
  | .pos atom => atom
  | .neg atom => atom

def formulaAtomsBelow (bound : Nat) (fmla : Sat.Fmla) : Bool :=
  fmla.all fun clause => clause.all fun literal =>
    decide (literalAtom literal < bound)

theorem baseFmla_atomsBelow :
    formulaAtomsBelow firstSelectorAtom
      (ProfileDFourRowCNF.fmla .uuu) = true := by
  decide

theorem baseFmla_literalAtom_lt
    (clause : Sat.Clause) (hclause : clause ∈ ProfileDFourRowCNF.fmla .uuu)
    (literal : Sat.Literal) (hliteral : List.Mem literal clause) :
    literalAtom literal < firstSelectorAtom := by
  have hformula := List.all_eq_true.mp baseFmla_atomsBelow
  have hclauseBelow := hformula clause hclause
  have hliterals := List.all_eq_true.mp hclauseBelow
  exact of_decide_eq_true (hliterals literal hliteral)

private theorem neg_iff_of_atom_iff
    (literal : Sat.Literal) (v w : Sat.Valuation)
    (h : v (literalAtom literal) ↔ w (literalAtom literal)) :
    v.neg literal ↔ w.neg literal := by
  cases literal <;> simp only [literalAtom, Sat.Valuation.neg] at h ⊢
  · exact not_congr h
  · exact h

private theorem satisfies_of_agrees_on_clause
    {v w : Sat.Valuation} (clause : Sat.Clause)
    (hagrees : ∀ literal, List.Mem literal clause →
      (v (literalAtom literal) ↔ w (literalAtom literal)))
    (hw : w.satisfies clause) : v.satisfies clause := by
  revert hagrees hw
  induction clause with
  | nil => intro _ hw; exact hw
  | cons literal tail ih =>
      intro hagrees hw hvneg
      apply ih
      · intro l hl
        exact hagrees l (List.Mem.tail literal hl)
      · apply hw
        exact (neg_iff_of_atom_iff literal v w
          (hagrees literal (List.Mem.head tail))).mp hvneg

theorem exact_satisfies_baseFmla (exact : ExactRepresentativeBranch) :
    (selectorValuation exact).satisfies_fmla
      (ProfileDFourRowCNF.fmla .uuu) := by
  have hbase := ProfileDFourRowCNF.fourExtension_satisfies_fmla
    (fourExtension exact.branch)
  constructor
  intro clause hclause
  apply satisfies_of_agrees_on_clause clause
  · intro literal hliteral
    exact selectorValuation_eq_below exact _
      (baseFmla_literalAtom_lt clause hclause literal hliteral)
  · exact hbase.prop clause hclause

/-! ## Satisfaction of the selector and ordinary-edge layers -/

theorem exact_satisfies_firstFourOwnUnitClauses
    (exact : ExactRepresentativeBranch) :
    (selectorValuation exact).satisfies_fmla firstFourOwnUnitClauses := by
  constructor
  intro clause hclause
  simp only [firstFourOwnUnitClauses, List.mem_map] at hclause
  obtain ⟨row, _hrow, rfl⟩ := hclause
  apply satisfies_of_mem_holds (selectorValuation exact)
    (l := Sat.Literal.pos (edgeAtom row.val selectedVertex.val 1))
  · exact List.Mem.head _
  · apply (selectorValuation_orderedEdgeAtom exact
      (ProfileDFourRowCNF.freeVertex row) selectedVertex 1 (by
        simp [ProfileDFourRowCNF.freeVertex, selectedVertex])).2
    change ProfileDFourRowCNF.totalColoring (fourExtension exact.branch)
        (ProfileDFourRowCNF.freeVertex row)
        (ProfileDFourRowCNF.tailVertex (blockVertex 0 0)) = 1
    simp [ProfileDFourRowCNF.totalColoring, pullbackColoring,
      ProfileDFourRowCNF.freeVertex, ProfileDFourRowCNF.tailVertex,
      ProfileDFourRowCNF.splitVertex, fourExtension,
      ProfileDUUUFourSupportP0SupportPair61.SelectedPosition,
      selectedVertex, joinColoring]
    exact exact.branch.firstFourOwn row

theorem exact_satisfies_pairExactlyOneClauses
    (exact : ExactRepresentativeBranch) :
    (selectorValuation exact).satisfies_fmla pairExactlyOneClauses := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hatLeast | hatMost
  · have hsingle : clause = pairAtLeastOneClause :=
      List.mem_singleton.mp hatLeast
    subst clause
    apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.pos (pairSelectorAtom exact.pair))
    · change Sat.Literal.pos (pairSelectorAtom exact.pair) ∈
        pairSelectorAtoms.map Sat.Literal.pos
      apply List.mem_map.mpr
      refine ⟨pairSelectorAtom exact.pair, ?_, rfl⟩
      simp [pairSelectorAtoms]
    · exact (selectorValuation_pairSelector exact exact.pair).2 rfl
  · simp only [pairAtMostOneClauses, List.mem_map] at hatMost
    obtain ⟨pair, hpair, rfl⟩ := hatMost
    obtain ⟨hleft, hright, hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    let left : SupportPair := Fin.ofNat 3 pair.1
    let right : SupportPair := Fin.ofNat 3 pair.2
    have hleftVal : left.val = pair.1 := by
      simp [left, Nat.mod_eq_of_lt hleft]
    have hrightVal : right.val = pair.2 := by
      simp [right, Nat.mod_eq_of_lt hright]
    have hlrFin : left < right := by
      change left.val < right.val
      omega
    by_cases hleftChosen : left = exact.pair
    · have hrightNot : right ≠ exact.pair := by
        intro hrightChosen
        exact (Fin.ne_of_lt hlrFin)
          (hleftChosen.trans hrightChosen.symm)
      apply satisfies_of_mem_holds (selectorValuation exact)
        (l := Sat.Literal.neg (pairSelectorAtom right))
      · exact List.Mem.tail _ (List.Mem.head _)
      · change ¬selectorValuation exact (pairSelectorAtom right)
        intro hselected
        exact hrightNot ((selectorValuation_pairSelector exact right).1
          hselected)
    · apply satisfies_of_mem_holds (selectorValuation exact)
        (l := Sat.Literal.neg (pairSelectorAtom left))
      · exact List.Mem.head _
      · change ¬selectorValuation exact (pairSelectorAtom left)
        intro hselected
        exact hleftChosen ((selectorValuation_pairSelector exact left).1
          hselected)

private theorem exact_firstSupport_edge
    (exact : ExactRepresentativeBranch) (p : Fin 15) :
    ProfileDFourRowCNF.totalColoring (fourExtension exact.branch)
        selectedVertex (firstForeignVertex p) = 1 ↔
      p ∈ pairFirstSupport exact.pair := by
  rw [show selectedVertex =
      ProfileDFourRowCNF.tailVertex
        (ProfileDTripleJoinReduction.blockVertex 0 0) by
        apply Fin.ext
        decide]
  rw [show firstForeignVertex p =
      ProfileDFourRowCNF.tailVertex
        (ProfileDTripleJoinReduction.blockVertex 1 p.val) by
        apply Fin.ext
        simp [firstForeignVertex, ProfileDFourRowCNF.tailVertex]
        rw [ProfileDTripleJoinReduction.blockVertex_val 1 p.isLt]
        rw [show blockStart (1 : Fin 3) = 15 by decide]
        omega]
  rw [ProfileDFourRowCNF.totalColoring_tail_tail]
  exact exact.firstSupportExact p

private theorem exact_secondSupport_edge
    (exact : ExactRepresentativeBranch) (p : Fin 16) :
    ProfileDFourRowCNF.totalColoring (fourExtension exact.branch)
        selectedVertex (secondForeignVertex p) = 1 ↔
      p ∈ pairSecondSupport exact.pair := by
  rw [show selectedVertex =
      ProfileDFourRowCNF.tailVertex
        (ProfileDTripleJoinReduction.blockVertex 0 0) by
        apply Fin.ext
        decide]
  rw [show secondForeignVertex p =
      ProfileDFourRowCNF.tailVertex
        (ProfileDTripleJoinReduction.blockVertex 2 p.val) by
        apply Fin.ext
        simp [secondForeignVertex, ProfileDFourRowCNF.tailVertex]
        rw [ProfileDTripleJoinReduction.blockVertex_val 2 p.isLt]
        rw [show blockStart (2 : Fin 3) = 30 by decide]
        omega]
  rw [ProfileDFourRowCNF.totalColoring_tail_tail]
  exact exact.secondSupportExact p

theorem exact_satisfies_supportGuardClauses
    (exact : ExactRepresentativeBranch) (pair : SupportPair) :
    (selectorValuation exact).satisfies_fmla
      (supportGuardClauses pair) := by
  constructor
  intro clause hclause
  by_cases hpair : pair = exact.pair
  · subst pair
    rcases List.mem_append.mp hclause with hfirst | hsecond
    · simp only [List.mem_map] at hfirst
      obtain ⟨p, _hpRange, rfl⟩ := hfirst
      by_cases hp : p ∈ pairFirstSupport exact.pair
      · apply satisfies_of_mem_holds (selectorValuation exact)
          (l := Sat.Literal.pos
            (edgeAtom selectedVertex.val (firstForeignVertex p).val 1))
        · exact List.Mem.tail _ (by
            simpa [supportLiteral, hp] using
              (List.Mem.head ([] : List Sat.Literal)))
        · apply (selectorValuation_orderedEdgeAtom exact selectedVertex
            (firstForeignVertex p) 1 (by
              simp [selectedVertex, firstForeignVertex]
              omega)).2
          exact (exact_firstSupport_edge exact p).2 hp
      · apply satisfies_of_mem_holds (selectorValuation exact)
          (l := Sat.Literal.neg
            (edgeAtom selectedVertex.val (firstForeignVertex p).val 1))
        · exact List.Mem.tail _ (by
            simpa [supportLiteral, hp] using
              (List.Mem.head ([] : List Sat.Literal)))
        · change ¬selectorValuation exact
            (edgeAtom selectedVertex.val (firstForeignVertex p).val 1)
          intro hedge
          have hcolor := (selectorValuation_orderedEdgeAtom exact
            selectedVertex (firstForeignVertex p) 1 (by
              simp [selectedVertex, firstForeignVertex]
              omega)).1 hedge
          exact hp ((exact_firstSupport_edge exact p).1 hcolor)
    · simp only [List.mem_map] at hsecond
      obtain ⟨p, _hpRange, rfl⟩ := hsecond
      by_cases hp : p ∈ pairSecondSupport exact.pair
      · apply satisfies_of_mem_holds (selectorValuation exact)
          (l := Sat.Literal.pos
            (edgeAtom selectedVertex.val (secondForeignVertex p).val 1))
        · exact List.Mem.tail _ (by
            simpa [supportLiteral, hp] using
              (List.Mem.head ([] : List Sat.Literal)))
        · apply (selectorValuation_orderedEdgeAtom exact selectedVertex
            (secondForeignVertex p) 1 (by
              simp [selectedVertex, secondForeignVertex]
              omega)).2
          exact (exact_secondSupport_edge exact p).2 hp
      · apply satisfies_of_mem_holds (selectorValuation exact)
          (l := Sat.Literal.neg
            (edgeAtom selectedVertex.val (secondForeignVertex p).val 1))
        · exact List.Mem.tail _ (by
            simpa [supportLiteral, hp] using
              (List.Mem.head ([] : List Sat.Literal)))
        · change ¬selectorValuation exact
            (edgeAtom selectedVertex.val (secondForeignVertex p).val 1)
          intro hedge
          have hcolor := (selectorValuation_orderedEdgeAtom exact
            selectedVertex (secondForeignVertex p) 1 (by
              simp [selectedVertex, secondForeignVertex]
              omega)).1 hedge
          exact hp ((exact_secondSupport_edge exact p).1 hcolor)
  · apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.neg (pairSelectorAtom pair))
    · rcases List.mem_append.mp hclause with hfirst | hsecond
      · obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hfirst
        exact List.Mem.head _
      · obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hsecond
        exact List.Mem.head _
    · change ¬selectorValuation exact (pairSelectorAtom pair)
      intro hselected
      exact hpair ((selectorValuation_pairSelector exact pair).1 hselected)

theorem exact_satisfies_matrixChoiceClause
    (exact : ExactRepresentativeBranch) (pair : SupportPair) :
    (selectorValuation exact).satisfies (matrixChoiceClause pair) := by
  by_cases hpair : pair = exact.pair
  · subst pair
    apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.pos (matrixSelectorAtom exact.selector))
    · apply List.Mem.tail
      apply List.mem_map.mpr
      refine ⟨exact.selector, ?_, rfl⟩
      apply List.mem_filter.mpr
      exact ⟨by simp, by simpa using exact.selectorPair⟩
    · exact (selectorValuation_matrixSelector exact exact.selector).2 rfl
  · apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.neg (pairSelectorAtom pair))
    · exact List.Mem.head _
    · change ¬selectorValuation exact (pairSelectorAtom pair)
      intro hselected
      exact hpair ((selectorValuation_pairSelector exact pair).1 hselected)

theorem exact_satisfies_matrixPairImplicationClause
    (exact : ExactRepresentativeBranch) (selector : MatrixSelector) :
    (selectorValuation exact).satisfies
      (matrixPairImplicationClause selector) := by
  by_cases hselector : selector = exact.selector
  · subst selector
    apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.pos
        (pairSelectorAtom (matrixPair exact.selector)))
    · exact List.Mem.tail _ (List.Mem.head _)
    · apply (selectorValuation_pairSelector exact
        (matrixPair exact.selector)).2
      exact exact.selectorPair
  · apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.neg (matrixSelectorAtom selector))
    · exact List.Mem.head _
    · change ¬selectorValuation exact (matrixSelectorAtom selector)
      intro hselected
      exact hselector
        ((selectorValuation_matrixSelector exact selector).1 hselected)

theorem exact_satisfies_matrixGuardClauses
    (exact : ExactRepresentativeBranch) (selector : MatrixSelector) :
    (selectorValuation exact).satisfies_fmla
      (matrixGuardClauses selector) := by
  constructor
  intro clause hclause
  simp only [matrixGuardClauses, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  by_cases hselector : selector = exact.selector
  · subst selector
    obtain ⟨hleft, hright, hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    let left : Fin 14 := matrixIndex pair.1
    let right : Fin 14 := matrixIndex pair.2
    have hleftVal : left.val = pair.1 := by
      simp [left, matrixIndex, Nat.mod_eq_of_lt hleft]
    have hrightVal : right.val = pair.2 := by
      simp [right, matrixIndex, Nat.mod_eq_of_lt hright]
    have hleftRight : left.val < right.val := by omega
    have hne : left ≠ right := Fin.ne_of_lt hleftRight
    let kind := pairSupportKind (matrixPair exact.selector)
    let leftVertex := physicalVertex kind left
    let rightVertex := physicalVertex kind right
    apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.pos (edgeAtom leftVertex.val rightVertex.val
        (representativeMatrixColor exact.selector left right).val))
    · exact List.Mem.tail _ (List.Mem.head _)
    · apply (selectorValuation_orderedEdgeAtom exact leftVertex rightVertex
        (representativeMatrixColor exact.selector left right) (by
          exact physicalVertex_strictMono kind hleftRight)).2
      change ProfileDFourRowCNF.totalColoring (fourExtension exact.branch)
          (physicalVertex (pairSupportKind (matrixPair exact.selector)) left)
          (physicalVertex (pairSupportKind (matrixPair exact.selector)) right) =
        representativeMatrixColor exact.selector left right
      rw [exact.selectorPair]
      exact exact.matrixExact left right hne
  · apply satisfies_of_mem_holds (selectorValuation exact)
      (l := Sat.Literal.neg (matrixSelectorAtom selector))
    · exact List.Mem.head _
    · change ¬selectorValuation exact (matrixSelectorAtom selector)
      intro hselected
      exact hselector
        ((selectorValuation_matrixSelector exact selector).1 hselected)

theorem exact_satisfies_matrixSelectorClauses
    (exact : ExactRepresentativeBranch) (selector : MatrixSelector) :
    (selectorValuation exact).satisfies_fmla
      (matrixSelectorClauses selector) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with himplication | hguards
  · have hsingle : clause = matrixPairImplicationClause selector :=
      List.mem_singleton.mp himplication
    subst clause
    exact exact_satisfies_matrixPairImplicationClause exact selector
  · exact (exact_satisfies_matrixGuardClauses exact selector).prop
      clause hguards

theorem exact_satisfies_pairBranchClauses
    (exact : ExactRepresentativeBranch) (pair : SupportPair) :
    (selectorValuation exact).satisfies_fmla (pairBranchClauses pair) := by
  constructor
  intro clause hclause
  simp only [pairBranchClauses, List.mem_append] at hclause
  rcases hclause with (hsupport | hchoice) | hmatrix
  · exact (exact_satisfies_supportGuardClauses exact pair).prop
      clause hsupport
  · have hsingle : clause = matrixChoiceClause pair :=
      List.mem_singleton.mp hchoice
    subst clause
    exact exact_satisfies_matrixChoiceClause exact pair
  · obtain ⟨selector, _hselector, hclause⟩ :=
      List.mem_flatMap.mp hmatrix
    exact (exact_satisfies_matrixSelectorClauses exact selector).prop
      clause hclause

theorem exact_satisfies_selectorFmla
    (exact : ExactRepresentativeBranch) :
    (selectorValuation exact).satisfies_fmla selectorFmla := by
  constructor
  intro clause hclause
  simp only [selectorFmla, List.mem_append] at hclause
  rcases hclause with (hfirstFour | hexactlyOne) | hpair
  · exact (exact_satisfies_firstFourOwnUnitClauses exact).prop
      clause hfirstFour
  · exact (exact_satisfies_pairExactlyOneClauses exact).prop
      clause hexactlyOne
  · obtain ⟨pair, _hpair, hclause⟩ := List.mem_flatMap.mp hpair
    exact (exact_satisfies_pairBranchClauses exact pair).prop clause hclause

/-- Exact semantic-to-formula bridge for one of the 36 representatives. -/
theorem exact_satisfies_fmla (exact : ExactRepresentativeBranch) :
    (selectorValuation exact).satisfies_fmla fmla := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hbase | hselectors
  · exact (exact_satisfies_baseFmla exact).prop clause hbase
  · exact (exact_satisfies_selectorFmla exact).prop clause hselectors

#print axioms fourExtension
#print axioms orderedEdgeAtom_lt_firstSelector
#print axioms baseFmla_atomsBelow
#print axioms exact_satisfies_baseFmla
#print axioms exact_satisfies_supportGuardClauses
#print axioms exact_satisfies_matrixGuardClauses
#print axioms exact_satisfies_selectorFmla
#print axioms exact_satisfies_fmla

end ProfileDUUUFourSupportP0SelectorBridge61
end R4333
