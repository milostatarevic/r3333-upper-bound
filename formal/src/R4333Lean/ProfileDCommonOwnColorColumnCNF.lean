import R4333Lean.ProfileDCompactFreeCompletionBlockZeroCNF

/-!
# Profile D with one common own-colour tail column

This target is deliberately separate from every row-incidence averaging
target.  Its semantic object is a native degree-floored profile-D four-row
extension together with one tail column `x` for which all four row entries
equal the omitted root colour `tailRootColor x`.

The exact SAT layer keeps all 46 possible columns.  It introduces one fresh
selector atom per column, one at-least-one selector clause, and four guarded
edge implications per column.  No at-most-one selector constraint and no
tail-template orbit normalization is used.  The addition is therefore
exactly `1 + 46 * 4 = 185` clauses.

The base contains only native compact lower/upper floors and the twelve
unconditional blockwise colour-zero hit clauses.  The profile-B/profile-C
conditional completion cuts are intentionally left for later layers.
-/

namespace R4333
namespace ProfileDCommonOwnColorColumnCNF

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ThresholdDegreeCapsCNF ColoringJoinRows
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDFourRowBoundary ProfileDFourRowDegreeCap
open ProfileDRowSupportBounds61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev FourExtension := ProfileDFourRowBoundary.FourExtension
abbrev DegreeFlooredFourExtension :=
  ProfileDRowSupportBounds61.DegreeFlooredFourExtension
abbrev compactCounterSpecs :=
  ProfileDCompactDegreeFlooredCNF.compactCounterSpecs

/-! ## Semantic object -/

structure CommonOwnColorColumnExtension (kind : Kind) : Type where
  toDegreeFlooredFourExtension : DegreeFlooredFourExtension kind
  column : TailVertex
  columnOwnColor : ∀ row : FourVertex,
    toDegreeFlooredFourExtension.toFourExtension.rows row column =
      tailRootColor column

/-- Bridge from the block/position form naturally produced by a high tail
endpoint to the column form consumed by this selector CNF. -/
def ofBlockColumn {kind : Kind}
    (ext : DegreeFlooredFourExtension kind)
    (block : Fin 3) (position : Fin (blockSize block))
    (hcommon : ∀ row : FourVertex,
      ext.toFourExtension.rows row (blockVertex block position.val) =
        Fin.succ block) :
    CommonOwnColorColumnExtension kind where
  toDegreeFlooredFourExtension := ext
  column := blockVertex block position.val
  columnOwnColor := by
    intro row
    have hroot : tailRootColor (blockVertex block position.val) =
        Fin.succ block := by
      fin_cases block <;>
        simp [tailRootColor, blockVertex_val, blockStart, blockSize] <;>
        omega
    rw [hroot]
    exact hcommon row

/-! ## Exact selector formula -/

/-- The first unused synthetic `K61` compact-counter vertex.  Existing
compact tags use synthetic vertices zero through seven, so vertex eight,
colour zero gives the immediately following leading tag `3753`.  Keeping
this tag dense avoids the very large paired atoms produced by a distant
namespace. -/
def selectorNamespaceVertex : Fin 61 := ⟨8, by omega⟩
def selectorNamespaceColor : Fin 4 := 0

def selectorNamespaceTag : Nat :=
  OutsideDegreeCapCNF.outsideDegreeCounterTag
    selectorNamespaceVertex selectorNamespaceColor

theorem selectorNamespaceTag_eq : selectorNamespaceTag = 3753 := by
  decide

def selectorAtom (x : TailVertex) : Nat :=
  Nat.pair selectorNamespaceTag x.val

theorem selectorAtom_dimacsVar_le (x : TailVertex) :
    dimacsVar (selectorAtom x) ≤ 14088808 := by
  fin_cases x <;> decide

def selectorAtoms : List Nat :=
  (List.finRange 46).map selectorAtom

def selectorAtLeastOneClause : Sat.Clause :=
  selectorAtoms.map Sat.Literal.pos

def guardedOwnColorClause (x : TailVertex)
    (row : FourVertex) : Sat.Clause :=
  [Sat.Literal.neg (selectorAtom x),
   Sat.Literal.pos
    (edgeAtom row.val (4 + x.val) (tailRootColor x).val)]

def guardedOwnColorClauses : Sat.Fmla :=
  (List.finRange 46).flatMap fun x =>
    (List.finRange 4).map (guardedOwnColorClause x)

def selectorFmla : Sat.Fmla :=
  [selectorAtLeastOneClause] ++ guardedOwnColorClauses

theorem selectorAtoms_length : selectorAtoms.length = 46 := by
  simp [selectorAtoms]

theorem guardedOwnColorClauses_length :
    guardedOwnColorClauses.length = 184 := by
  simp [guardedOwnColorClauses]

theorem selectorFmla_length : selectorFmla.length = 185 := by
  simp [selectorFmla, guardedOwnColorClauses]

/-! ## Native compact floors plus unconditional block-zero clauses -/

def nativeBlockZeroBaseFmla (kind : Kind) : Sat.Fmla :=
  ProfileDCompactDegreeFlooredCNF.compactBaseFmla kind ++
    ProfileDCompactFreeCompletionBlockZeroCNF.blockZeroHitClauses

def nativeBlockZeroFmla (kind : Kind) : Sat.Fmla :=
  manySequentialAtMostFmla
    (nativeBlockZeroBaseFmla kind) compactCounterSpecs

theorem nativeBlockZeroBaseFmla_length (kind : Kind) :
    (nativeBlockZeroBaseFmla kind).length = 88795 := by
  simp [nativeBlockZeroBaseFmla,
    ProfileDCompactDegreeFlooredCNF.compactBaseFmla_length,
    ProfileDCompactFreeCompletionBlockZeroCNF.blockZeroHitClauses_length]

theorem nativeBlockZeroFmla_length (kind : Kind) :
    (nativeBlockZeroFmla kind).length = 165899 := by
  rw [nativeBlockZeroFmla, manySequentialAtMostFmla_length,
    nativeBlockZeroBaseFmla_length,
    ProfileDCompactDegreeFlooredCNF.compactCounterClauseContribution]

def fmla (kind : Kind) : Sat.Fmla :=
  nativeBlockZeroFmla kind ++ selectorFmla

theorem fmla_length (kind : Kind) : (fmla kind).length = 166084 := by
  simp [fmla, nativeBlockZeroFmla_length, selectorFmla_length]

/-! ## Well-formed native counter composition -/

theorem nativeBlockZeroCounterSpecs_wellFormed (kind : Kind) :
    ManyCounterWellFormed
      (nativeBlockZeroBaseFmla kind) compactCounterSpecs := by
  let old :=
    ProfileDCompactDegreeFlooredCNF.compactCounterSpecs_wellFormed kind
  refine ⟨old.tags_nodup, ?_, old.inputs_outside⟩
  intro reserved hreserved
  unfold nativeBlockZeroBaseFmla
  apply formulaOutsideNamespace_append
  · exact old.base_outside reserved hreserved
  · have hreserved' : reserved ∈ compactCounterSpecs := hreserved
    simp only [compactCounterSpecs,
      ProfileDCompactDegreeFlooredCNF.compactCounterSpecs,
      List.mem_map] at hreserved'
    obtain ⟨⟨row, color, phase⟩, _hcontext, rfl⟩ := hreserved'
    exact
      ProfileDCompactFreeCompletionBlockZeroCNF.blockZeroHitClauses_outside_largerCounterNamespace
        (n := 61) (by omega)
        (ProfileDCompactDegreeFlooredCNF.compactNamespaceVertex row phase)
        color

theorem degreeFloored_satisfies_nativeBlockZeroFmla
    {kind : Kind} (ext : DegreeFlooredFourExtension kind) :
    (iteratedSequentialExtension compactCounterSpecs
      (ProfileDCompactDegreeFlooredCNF.complementValuation
        ext.toFourExtension)).satisfies_fmla
          (nativeBlockZeroFmla kind) := by
  apply iteratedExtension_satisfies_manySequentialAtMostFmla
    (nativeBlockZeroBaseFmla kind) compactCounterSpecs
    (ProfileDCompactDegreeFlooredCNF.complementValuation
      ext.toFourExtension)
    (nativeBlockZeroCounterSpecs_wellFormed kind)
  · constructor
    intro clause hclause
    rcases List.mem_append.mp hclause with hcompact | hzero
    · rcases List.mem_append.mp hcompact with hraw | hdefinitions
      · exact
          (ProfileDCompactDegreeFlooredCNF.complementValuation_satisfies_rawFmla
            ext.toFourExtension).prop clause hraw
      · exact
          (ProfileDCompactDegreeFlooredCNF.complementValuation_satisfies_definitions
            ext.toFourExtension).prop clause hdefinitions
    · exact
        (ProfileDCompactFreeCompletionBlockZeroCNF.complementValuation_satisfies_blockZeroHitClauses
          ext).prop clause hzero
  · exact ProfileDCompactDegreeFlooredCNF.allCaps_of_degreeFlooredFourExtension
      ext

/-! ## Selector namespace separation -/

theorem complementNamespaceTag_ne_selectorNamespaceTag :
    ProfileDCompactDegreeFlooredCNF.complementNamespaceTag ≠
      selectorNamespaceTag := by
  simp [ProfileDCompactDegreeFlooredCNF.complementNamespaceTag,
    ProfileDCompactDegreeFlooredCNF.complementNamespaceVertex,
    ProfileDCompactDegreeFlooredCNF.complementNamespaceColor,
    selectorNamespaceTag, selectorNamespaceVertex,
    selectorNamespaceColor,
    OutsideDegreeCapCNF.outsideDegreeCounterTag]

theorem compactCounterTag_ne_selectorNamespaceTag
    (row color : Fin 4)
    (phase : ProfileDCompactDegreeFlooredCNF.CounterPhase) :
    ProfileDCompactDegreeFlooredCNF.compactCounterTag row color phase ≠
      selectorNamespaceTag := by
  simp [ProfileDCompactDegreeFlooredCNF.compactCounterTag,
    ProfileDCompactDegreeFlooredCNF.compactNamespaceVertex,
    selectorNamespaceTag, selectorNamespaceVertex,
    selectorNamespaceColor,
    OutsideDegreeCapCNF.outsideDegreeCounterTag]
  omega

private theorem compactInputs_outside_selectorNamespace
    (row color : Fin 4)
    (phase : ProfileDCompactDegreeFlooredCNF.CounterPhase) :
    InputsOutsideNamespace selectorNamespaceTag
      (ProfileDCompactDegreeFlooredCNF.compactContextInputs
        row color phase) := by
  by_cases hphase : phase = ProfileDDegreeFlooredCNF.upperPhase
  · simp only [ProfileDCompactDegreeFlooredCNF.compactContextInputs,
      hphase, if_pos]
    exact
      ProfileDCompactDegreeFlooredCNF.rowColorAtoms_outside_largerCounterNamespace
        (n := 61) (by omega) selectorNamespaceVertex
        selectorNamespaceColor row color
  · simp only [ProfileDCompactDegreeFlooredCNF.compactContextInputs,
      hphase]
    exact ComplementAtomCNF.complementAtoms_outside_otherNamespace
      complementNamespaceTag_ne_selectorNamespaceTag _

theorem nativeBlockZeroBaseFmla_outside_selectorNamespace (kind : Kind) :
    FormulaOutsideNamespace selectorNamespaceTag
      (nativeBlockZeroBaseFmla kind) := by
  unfold nativeBlockZeroBaseFmla
  apply formulaOutsideNamespace_append
  · unfold ProfileDCompactDegreeFlooredCNF.compactBaseFmla
    apply formulaOutsideNamespace_append
    · exact ProfileDCompactDegreeFlooredCNF.rawFmla_outside_largerCounterNamespace
        (n := 61) (by omega) kind selectorNamespaceVertex
        selectorNamespaceColor
    · exact ComplementAtomCNF.complementDefinitionClauses_outside_otherNamespace
        complementNamespaceTag_ne_selectorNamespaceTag
        ProfileDCompactDegreeFlooredCNF.complementSourceAtom
        ProfileDCompactDegreeFlooredCNF.complementKeys
        (ProfileDCompactDegreeFlooredCNF.complementSourceAtoms_outside_largerCounterNamespace
          (n := 61) (by omega) selectorNamespaceVertex
          selectorNamespaceColor)
  · exact
      ProfileDCompactFreeCompletionBlockZeroCNF.blockZeroHitClauses_outside_largerCounterNamespace
        (n := 61) (by omega) selectorNamespaceVertex
        selectorNamespaceColor

theorem nativeBlockZeroFmla_outside_selectorNamespace (kind : Kind) :
    FormulaOutsideNamespace selectorNamespaceTag
      (nativeBlockZeroFmla kind) := by
  rw [nativeBlockZeroFmla, manySequentialAtMostFmla_eq_append_flatMap]
  apply formulaOutsideNamespace_append
  · exact nativeBlockZeroBaseFmla_outside_selectorNamespace kind
  · intro clause hclause literal hliteral
    obtain ⟨spec, hspec, hcounter⟩ := List.mem_flatMap.mp hclause
    have hspec' : spec ∈ compactCounterSpecs := hspec
    simp only [compactCounterSpecs,
      ProfileDCompactDegreeFlooredCNF.compactCounterSpecs,
      List.mem_map] at hspec'
    obtain ⟨⟨row, color, phase⟩, _hcontext, rfl⟩ := hspec'
    exact SequentialAtMostManyCNF.counterBlock_outside_other_namespace
      (ProfileDCompactDegreeFlooredCNF.compactCounterSpec
        (row, color, phase)) selectorNamespaceTag
      (compactCounterTag_ne_selectorNamespaceTag row color phase)
      (compactInputs_outside_selectorNamespace row color phase)
      clause hcounter literal hliteral

/-! ## Explicit selector valuation -/

/-- Set exactly the selected key true inside the selector namespace and
retain the native compact valuation everywhere else. -/
noncomputable def selectorExtendedValuation
    (selected : TailVertex) (base : Sat.Valuation) : Sat.Valuation :=
  fun atom =>
    @ite Prop (InSequentialNamespace selectorNamespaceTag atom)
      (Classical.propDecidable _)
      ((Nat.unpair atom).2 = selected.val)
      (base atom)

theorem selectorExtendedValuation_eq_of_outside
    (selected : TailVertex) (base : Sat.Valuation) (atom : Nat)
    (houtside : ¬InSequentialNamespace selectorNamespaceTag atom) :
    selectorExtendedValuation selected base atom ↔ base atom := by
  simp [selectorExtendedValuation, houtside]

@[simp] theorem selectorExtendedValuation_selectorAtom
    (selected x : TailVertex) (base : Sat.Valuation) :
    selectorExtendedValuation selected base (selectorAtom x) ↔
      x = selected := by
  simp only [selectorExtendedValuation, selectorAtom,
    InSequentialNamespace, Nat.unpair_pair, ↓reduceIte]
  constructor
  · intro h
    exact Fin.ext h
  · intro h
    exact congrArg Fin.val h

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

theorem selectorExtendedValuation_satisfies_base
    (selected : TailVertex) (base : Sat.Valuation)
    (baseFmla : Sat.Fmla)
    (houtside : FormulaOutsideNamespace selectorNamespaceTag baseFmla)
    (hbase : base.satisfies_fmla baseFmla) :
    (selectorExtendedValuation selected base).satisfies_fmla baseFmla := by
  constructor
  intro clause hclause
  apply satisfies_of_agrees_on_clause clause
  · intro literal hliteral
    exact selectorExtendedValuation_eq_of_outside selected base _
      (houtside clause hclause literal hliteral)
  · exact hbase.prop clause hclause

/-! ## Ordinary edge semantics under the native compact valuation -/

noncomputable def nativeValuation {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) : Sat.Valuation :=
  iteratedSequentialExtension compactCounterSpecs
    (ProfileDCompactDegreeFlooredCNF.complementValuation
      ext.toFourExtension)

private theorem iteratedSequentialExtension_eq_of_outside_all
    (specs : List CounterSpec) (v : Sat.Valuation) (atom : Nat)
    (houtside : ∀ spec, spec ∈ specs →
      ¬InSequentialNamespace spec.tag atom) :
    iteratedSequentialExtension specs v atom ↔ v atom := by
  induction specs generalizing v with
  | nil => rfl
  | cons head tail ih =>
      rw [iteratedSequentialExtension_cons]
      exact (ih (sequentialExtension head.tag head.inputs v) (by
        intro spec hspec
        exact houtside spec (List.Mem.tail head hspec))).trans
          (sequentialExtension_eq_of_outside head.tag head.inputs v
            (houtside head (List.Mem.head tail)))

private theorem rowEdgeAtom_outside_all_compactCounters
    (x : TailVertex) (row color : FourVertex) :
    ∀ spec, spec ∈ compactCounterSpecs →
      ¬InSequentialNamespace spec.tag
        (edgeAtom row.val (4 + x.val) color.val) := by
  intro spec hspec
  have hspec' := hspec
  simp only [compactCounterSpecs,
    ProfileDCompactDegreeFlooredCNF.compactCounterSpecs,
    List.mem_map] at hspec'
  obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hspec'
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    (ProfileDCompactDegreeFlooredCNF.compactNamespaceVertex a phase) q
    (by omega) (by omega)

theorem nativeValuation_rowTailAtom {kind : Kind}
    (ext : DegreeFlooredFourExtension kind)
    (x : TailVertex) (row color : FourVertex) :
    nativeValuation ext (edgeAtom row.val (4 + x.val) color.val) ↔
      ext.toFourExtension.rows row x = color := by
  let atom := edgeAtom row.val (4 + x.val) color.val
  calc
    nativeValuation ext atom ↔
        ProfileDCompactDegreeFlooredCNF.complementValuation
          ext.toFourExtension atom := by
      exact
        iteratedSequentialExtension_eq_of_outside_all
          compactCounterSpecs _ atom
          (rowEdgeAtom_outside_all_compactCounters x row color)
    _ ↔ coloringValuation
          (ProfileDFourRowCNF.totalColoring ext.toFourExtension) atom := by
      apply ComplementAtomCNF.complementExtension_eq_of_outside
      exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        ProfileDCompactDegreeFlooredCNF.complementNamespaceVertex
        ProfileDCompactDegreeFlooredCNF.complementNamespaceColor
        (by omega) (by omega)
    _ ↔ ext.toFourExtension.rows row x = color := by
      have hedge := coloringValuation_edgeAtom
        (ProfileDFourRowCNF.totalColoring ext.toFourExtension)
        (ProfileDFourRowCNF.freeVertex row)
        (ProfileDFourRowCNF.tailVertex x) color
      rw [ProfileDFromBFreeCompletionCNF.totalColoring_free_tail] at hedge
      simpa [atom, ProfileDFourRowCNF.freeVertex,
        ProfileDFourRowCNF.tailVertex] using hedge

theorem selectorExtendedValuation_satisfies_selectorFmla
    {kind : Kind} (ext : CommonOwnColorColumnExtension kind) :
    (selectorExtendedValuation ext.column
      (nativeValuation ext.toDegreeFlooredFourExtension)).satisfies_fmla
        selectorFmla := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hatLeast | hguarded
  · have hsingle : clause = selectorAtLeastOneClause :=
      List.mem_singleton.mp hatLeast
    subst clause
    apply satisfies_of_mem_holds
      (selectorExtendedValuation ext.column
        (nativeValuation ext.toDegreeFlooredFourExtension))
      (l := Sat.Literal.pos (selectorAtom ext.column))
    · change Sat.Literal.pos (selectorAtom ext.column) ∈
        selectorAtoms.map Sat.Literal.pos
      apply List.mem_map.mpr
      exact ⟨selectorAtom ext.column, by
        simp [selectorAtoms], rfl⟩
    · exact (selectorExtendedValuation_selectorAtom
        ext.column ext.column _).2 rfl
  · obtain ⟨x, _hx, hrowClause⟩ := List.mem_flatMap.mp hguarded
    obtain ⟨row, _hrow, rfl⟩ := List.mem_map.mp hrowClause
    by_cases hx : x = ext.column
    · subst x
      apply satisfies_of_mem_holds
        (selectorExtendedValuation ext.column
          (nativeValuation ext.toDegreeFlooredFourExtension))
        (l := Sat.Literal.pos
          (edgeAtom row.val (4 + ext.column.val)
            (tailRootColor ext.column).val))
      · exact List.Mem.tail _ (List.Mem.head _)
      · apply (selectorExtendedValuation_eq_of_outside
          ext.column (nativeValuation ext.toDegreeFlooredFourExtension) _
          (OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
            selectorNamespaceVertex selectorNamespaceColor
            (by omega) (by omega))).2
        exact (nativeValuation_rowTailAtom
          ext.toDegreeFlooredFourExtension ext.column row
          (tailRootColor ext.column)).2 (ext.columnOwnColor row)
    · apply satisfies_of_mem_holds
        (selectorExtendedValuation ext.column
          (nativeValuation ext.toDegreeFlooredFourExtension))
        (l := Sat.Literal.neg (selectorAtom x))
      · exact List.Mem.head _
      · change ¬selectorExtendedValuation ext.column
          (nativeValuation ext.toDegreeFlooredFourExtension)
            (selectorAtom x)
        intro hselected
        exact hx ((selectorExtendedValuation_selectorAtom
          ext.column x _).1 hselected)

noncomputable def finalValuation {kind : Kind}
    (ext : CommonOwnColorColumnExtension kind) : Sat.Valuation :=
  selectorExtendedValuation ext.column
    (nativeValuation ext.toDegreeFlooredFourExtension)

theorem commonColumnExtension_satisfies_fmla {kind : Kind}
    (ext : CommonOwnColorColumnExtension kind) :
    (finalValuation ext).satisfies_fmla (fmla kind) := by
  have hbase := selectorExtendedValuation_satisfies_base
    ext.column (nativeValuation ext.toDegreeFlooredFourExtension)
    (nativeBlockZeroFmla kind)
    (nativeBlockZeroFmla_outside_selectorNamespace kind)
    (degreeFloored_satisfies_nativeBlockZeroFmla
      ext.toDegreeFlooredFourExtension)
  have hselector := selectorExtendedValuation_satisfies_selectorFmla ext
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · exact hbase.prop clause hclause
  · exact hselector.prop clause hclause

/-! ## LRAT endpoints -/

theorem noCommonOwnColorColumnExtension_of_lrat (kind : Kind)
    (hunsat : (fmla kind).proof []) :
    ¬Nonempty (CommonOwnColorColumnExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat (finalValuation ext)
    (commonColumnExtension_satisfies_fmla ext)

structure AllKindLRATRefutations : Prop where
  uuu : (fmla .uuu).proof []
  uut : (fmla .uut).proof []
  utu : (fmla .utu).proof []
  utt : (fmla .utt).proof []
  tuu : (fmla .tuu).proof []
  tut : (fmla .tut).proof []
  ttu : (fmla .ttu).proof []
  ttt : (fmla .ttt).proof []

theorem AllKindLRATRefutations.obstruction
    (h : AllKindLRATRefutations) (kind : Kind) :
    ¬Nonempty (CommonOwnColorColumnExtension kind) := by
  cases kind with
  | uuu => exact noCommonOwnColorColumnExtension_of_lrat .uuu h.uuu
  | uut => exact noCommonOwnColorColumnExtension_of_lrat .uut h.uut
  | utu => exact noCommonOwnColorColumnExtension_of_lrat .utu h.utu
  | utt => exact noCommonOwnColorColumnExtension_of_lrat .utt h.utt
  | tuu => exact noCommonOwnColorColumnExtension_of_lrat .tuu h.tuu
  | tut => exact noCommonOwnColorColumnExtension_of_lrat .tut h.tut
  | ttu => exact noCommonOwnColorColumnExtension_of_lrat .ttu h.ttu
  | ttt => exact noCommonOwnColorColumnExtension_of_lrat .ttt h.ttt

#print axioms R4333.ProfileDCommonOwnColorColumnCNF.nativeBlockZeroCounterSpecs_wellFormed
#print axioms R4333.ProfileDCommonOwnColorColumnCNF.nativeBlockZeroFmla_outside_selectorNamespace
#print axioms R4333.ProfileDCommonOwnColorColumnCNF.nativeValuation_rowTailAtom
#print axioms R4333.ProfileDCommonOwnColorColumnCNF.commonColumnExtension_satisfies_fmla
#print axioms R4333.ProfileDCommonOwnColorColumnCNF.noCommonOwnColorColumnExtension_of_lrat

end ProfileDCommonOwnColorColumnCNF
end R4333
