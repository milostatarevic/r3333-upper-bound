import R4333Lean.ComplementAtomCNF
import R4333Lean.ProfileDConditionalCompletionCNF
import R4333Lean.ProfileDDegreeFlooredCNF

/-!
# Compact exact degree-floor formulas for profile D

The earlier degree-floor formula expresses each lower support bound by
counting 138 atoms in the other three colours.  Here every one of the
`4 * 4 * 46 = 736` row/colour/tail incidences receives one explicitly
defined complement atom.  Two clauses define each complement, after which
every lower counter has only 46 inputs.  Upper counters are unchanged.

Freshness is structural:

* complement atoms use the standard `K_60` degree tag 3600;
* the 32 counters use distinct standard `K_61` degree tags 3721--3752;
* existing `K_50` degree and floor tags occupy 2500--2699.

Thus edge atoms, complement atoms, compact counters, and every existing
degree/floor counter namespace are pairwise separated where required.
No checked-refutation inhabitant is supplied.
-/

namespace R4333
namespace ProfileDCompactDegreeFlooredCNF

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDRowSupportBounds61

set_option maxRecDepth 1000000

abbrev CounterPhase := ProfileDDegreeFlooredCNF.CounterPhase
abbrev CounterContext := ProfileDDegreeFlooredCNF.CounterContext
abbrev ComplementContext := FourVertex × (Fin 4 × TailVertex)

/-! ## Fresh atom namespaces -/

def complementNamespaceVertex : Fin 60 := 0
def complementNamespaceColor : Fin 4 := 0

/-- This reduces to 3600, above every leading endpoint-pair code on K50. -/
def complementNamespaceTag : Nat :=
  OutsideDegreeCapCNF.outsideDegreeCounterTag
    complementNamespaceVertex complementNamespaceColor

/-- Eight synthetic K61 vertices encode `(row, phase)`. -/
def compactNamespaceVertex (a : FourVertex)
    (phase : CounterPhase) : Fin 61 :=
  ⟨a.val * 2 + phase.val, by omega⟩

theorem compactNamespaceVertex_injective :
    Function.Injective
      (fun ap : FourVertex × CounterPhase =>
        compactNamespaceVertex ap.1 ap.2) := by
  decide

/-- Compact counter tags reduce to the interval 3721--3752. -/
def compactCounterTag (a : FourVertex) (q : Fin 4)
    (phase : CounterPhase) : Nat :=
  OutsideDegreeCapCNF.outsideDegreeCounterTag
    (compactNamespaceVertex a phase) q

theorem compactCounterTag_injective :
    Function.Injective (fun context : CounterContext =>
      compactCounterTag context.1 context.2.1 context.2.2) := by
  rintro ⟨a, q, phase⟩ ⟨b, r, otherPhase⟩ h
  obtain ⟨hvertex, hcolor⟩ :=
    OutsideDegreeCapCNF.outsideDegreeCounterTag_injective h
  have hap : (a, phase) = (b, otherPhase) :=
    compactNamespaceVertex_injective hvertex
  cases hap
  cases hcolor
  rfl

theorem complementNamespaceTag_ne_compactCounterTag
    (a : FourVertex) (q : Fin 4) (phase : CounterPhase) :
    complementNamespaceTag ≠ compactCounterTag a q phase := by
  simp [complementNamespaceTag, complementNamespaceVertex,
    complementNamespaceColor, compactCounterTag,
    compactNamespaceVertex,
    OutsideDegreeCapCNF.outsideDegreeCounterTag]
  omega

/-- Formal separation from all existing K50 degree-cap and floor tags. -/
theorem complementNamespaceTag_ne_existingDegreeTag
    (x : Fin 50) (q : Fin 4) :
    complementNamespaceTag ≠
      OutsideDegreeCapCNF.outsideDegreeCounterTag x q := by
  simp [complementNamespaceTag, complementNamespaceVertex,
    complementNamespaceColor,
    OutsideDegreeCapCNF.outsideDegreeCounterTag]
  omega

theorem compactCounterTag_ne_existingDegreeTag
    (a : FourVertex) (q : Fin 4) (phase : CounterPhase)
    (x : Fin 50) (r : Fin 4) :
    compactCounterTag a q phase ≠
      OutsideDegreeCapCNF.outsideDegreeCounterTag x r := by
  simp [compactCounterTag, compactNamespaceVertex,
    OutsideDegreeCapCNF.outsideDegreeCounterTag]
  omega

/-! ## The 736 complement atoms and their definitions -/

/-- Pairing key for one `(row, colour, tail position)` incidence. -/
def complementKey (a : FourVertex) (q : Fin 4)
    (x : TailVertex) : Nat :=
  Nat.pair (Nat.pair a.val q.val) x.val

theorem complementKey_injective :
    Function.Injective (fun context : ComplementContext =>
      complementKey context.1 context.2.1 context.2.2) := by
  rintro ⟨a, q, x⟩ ⟨b, r, y⟩ h
  have houter := Nat.pair_eq_pair.mp h
  have hinner := Nat.pair_eq_pair.mp houter.1
  exact Prod.ext (Fin.ext hinner.1)
    (Prod.ext (Fin.ext hinner.2) (Fin.ext houter.2))

/-- Decode a complement key to the corresponding row-tail colour atom.
Out-of-range decoded keys are harmless because only the 736 valid keys are
used in clauses and counter inputs. -/
def complementSourceAtom (key : Nat) : Nat :=
  let outer := Nat.unpair key
  let rowColor := Nat.unpair outer.1
  edgeAtom rowColor.1 (4 + outer.2) rowColor.2

@[simp] theorem complementSourceAtom_key
    (a : FourVertex) (q : Fin 4) (x : TailVertex) :
    complementSourceAtom (complementKey a q x) =
      edgeAtom a.val (4 + x.val) q.val := by
  simp [complementSourceAtom, complementKey, Nat.unpair_pair]

def complementContexts : List ComplementContext :=
  (List.finRange 4).product
    ((List.finRange 4).product (List.finRange 46))

theorem complementContexts_length : complementContexts.length = 736 := by
  calc
    complementContexts.length =
        (List.finRange 4).length *
          ((List.finRange 4).product (List.finRange 46)).length :=
      List.length_product _ _
    _ = (List.finRange 4).length *
        ((List.finRange 4).length * (List.finRange 46).length) := by
      exact congrArg (fun n => (List.finRange 4).length * n)
        (List.length_product (List.finRange 4) (List.finRange 46))
    _ = 736 := by simp

theorem complementContexts_nodup : complementContexts.Nodup := by
  exact (List.nodup_finRange 4).product
    ((List.nodup_finRange 4).product (List.nodup_finRange 46))

def complementKeys : List Nat :=
  complementContexts.map fun context =>
    complementKey context.1 context.2.1 context.2.2

theorem complementKeys_length : complementKeys.length = 736 := by
  simp [complementKeys, complementContexts_length]

theorem complementKeys_nodup : complementKeys.Nodup := by
  exact complementContexts_nodup.map complementKey_injective

def rowColorKeys (a : FourVertex) (q : Fin 4) : List Nat :=
  (List.finRange 46).map fun x => complementKey a q x

theorem rowColorKeys_length (a : FourVertex) (q : Fin 4) :
    (rowColorKeys a q).length = 46 := by
  simp [rowColorKeys]

theorem rowColorKeys_nodup (a : FourVertex) (q : Fin 4) :
    (rowColorKeys a q).Nodup := by
  apply (List.nodup_finRange 46).map
  intro x y h
  have houter := Nat.pair_eq_pair.mp h
  exact Fin.ext houter.2

theorem rowColorKeys_map_sourceAtom
    (a : FourVertex) (q : Fin 4) :
    (rowColorKeys a q).map complementSourceAtom =
      ProfileDDegreeFlooredCNF.rowColorAtoms a q := by
  simp [rowColorKeys, ProfileDDegreeFlooredCNF.rowColorAtoms,
    List.map_map, Function.comp_def]

/-- The actual fresh atom for one row/colour/tail incidence. -/
def rowComplementAtom (a : FourVertex) (q : Fin 4)
    (x : TailVertex) : Nat :=
  ComplementAtomCNF.complementAtom complementNamespaceTag
    (complementKey a q x)

theorem rowComplementAtom_injective :
    Function.Injective (fun context : ComplementContext =>
      rowComplementAtom context.1 context.2.1 context.2.2) := by
  intro left right h
  apply complementKey_injective
  exact ComplementAtomCNF.complementAtom_injective
    complementNamespaceTag h

/-- Exactly 46 positive complement inputs for one lower counter. -/
def compactLowerInputs (a : FourVertex) (q : Fin 4) : List Nat :=
  ComplementAtomCNF.complementAtoms complementNamespaceTag
    (rowColorKeys a q)

theorem compactLowerInputs_length (a : FourVertex) (q : Fin 4) :
    (compactLowerInputs a q).length = 46 := by
  simp [compactLowerInputs, ComplementAtomCNF.complementAtoms_length,
    rowColorKeys_length]

theorem compactLowerInputs_nodup (a : FourVertex) (q : Fin 4) :
    (compactLowerInputs a q).Nodup :=
  ComplementAtomCNF.complementAtoms_nodup
    complementNamespaceTag (rowColorKeys_nodup a q)

/-- The authoritative 1,472-clause complement-definition block. -/
def complementDefinitionClauses : Sat.Fmla :=
  ComplementAtomCNF.complementDefinitionClauses
    complementNamespaceTag complementSourceAtom complementKeys

theorem complementDefinitionClauses_length :
    complementDefinitionClauses.length = 1472 := by
  rw [complementDefinitionClauses,
    ComplementAtomCNF.complementDefinitionClauses_length,
    complementKeys_length]

/-! ## Formula namespace facts -/

theorem goodColoringFmla50_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (goodColoringFmla 50 4) := by
  intro clause hclause literal hliteral
  change clause ∈
    (atLeastOneClauses 50 4 ++ atMostOneClauses 50 4) ++
      triangleClauses 50 4 at hclause
  rcases List.mem_append.mp hclause with hleft | htriangle
  rcases List.mem_append.mp hleft with hatLeast | hatMost
  · simp only [atLeastOneClauses, List.mem_map] at hatLeast
    obtain ⟨⟨a, b⟩, hedge, rfl⟩ := hatLeast
    have hliteral' : literal ∈
        ((List.range 4).map fun q => Sat.Literal.pos (edgeAtom a b q)) :=
      hliteral
    simp only [List.mem_map] at hliteral'
    obtain ⟨q, _hq, rfl⟩ := hliteral'
    obtain ⟨ha, hb, _hab⟩ := SingleRootStarCNF.mem_edges_bounds hedge
    exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
      reservedX reservedQ (by omega) (by omega)
  · simp only [atMostOneClauses, List.mem_flatMap,
      List.mem_map] at hatMost
    obtain ⟨⟨a, b⟩, hedge, ⟨⟨q, r⟩, _hqr, rfl⟩⟩ := hatMost
    obtain ⟨ha, hb, _hab⟩ := SingleRootStarCNF.mem_edges_bounds hedge
    rcases List.mem_cons.mp hliteral with hfirst | htail
    · subst literal
      exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        reservedX reservedQ (lt_of_lt_of_le ha hn) (lt_of_lt_of_le hb hn)
    · have hsecond := List.mem_singleton.mp htail
      subst literal
      exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        reservedX reservedQ (by omega) (by omega)
  · simp only [triangleClauses, List.mem_flatMap,
      List.mem_map] at htriangle
    obtain ⟨⟨a, b, d⟩, htriple, ⟨q, _hq, rfl⟩⟩ := htriangle
    obtain ⟨ha, hb, hd, _hab, _hbd⟩ :=
      FiniteColorCNF.mem_triples_iff_bounds htriple
    rcases List.mem_cons.mp hliteral with hfirst | htail
    · subst literal
      exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        reservedX reservedQ (lt_of_lt_of_le ha hn) (lt_of_lt_of_le hb hn)
    · rcases List.mem_cons.mp htail with hsecond | hlast
      · subst literal
        exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
          reservedX reservedQ (lt_of_lt_of_le ha hn) (lt_of_lt_of_le hd hn)
      · have hthird := List.mem_singleton.mp hlast
        subst literal
        exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
          reservedX reservedQ (lt_of_lt_of_le hb hn) (lt_of_lt_of_le hd hn)

private theorem blockTemplateUnitClauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (kind : Kind) (block : Fin 3)
    (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (ProfileDFourRowCNF.blockTemplateUnitClauses kind block) := by
  unfold ProfileDFourRowCNF.blockTemplateUnitClauses
  apply ThresholdDegreeCapsCNF.positiveEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    obtain ⟨hleft, _hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega
  · intro pair hpair
    obtain ⟨_left, hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega

private theorem templateUnitClauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (kind : Kind)
    (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (ProfileDFourRowCNF.templateUnitClauses kind) := by
  unfold ProfileDFourRowCNF.templateUnitClauses
  apply ThresholdDegreeCapsCNF.formulaOutsideNamespace_append
  · apply ThresholdDegreeCapsCNF.formulaOutsideNamespace_append
    · exact blockTemplateUnitClauses_outside_largerCounterNamespace
        hn kind 0 reservedX reservedQ
    · exact blockTemplateUnitClauses_outside_largerCounterNamespace
        hn kind 1 reservedX reservedQ
  · exact blockTemplateUnitClauses_outside_largerCounterNamespace
      hn kind 2 reservedX reservedQ

private theorem insideRootForbiddenUnitClauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      ProfileDFourRowCNF.insideRootForbiddenUnitClauses := by
  unfold ProfileDFourRowCNF.insideRootForbiddenUnitClauses
  apply ThresholdDegreeCapsCNF.negativeEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    have := (SingleRootStarCNF.mem_edges_bounds hpair).1
    omega
  · intro pair hpair
    have := (SingleRootStarCNF.mem_edges_bounds hpair).2.1
    omega

theorem rawFmla_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (kind : Kind)
    (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (ProfileDFourRowCNF.fmla kind) := by
  unfold ProfileDFourRowCNF.fmla
  apply ThresholdDegreeCapsCNF.formulaOutsideNamespace_append
  · apply ThresholdDegreeCapsCNF.formulaOutsideNamespace_append
    · exact goodColoringFmla50_outside_largerCounterNamespace
        hn reservedX reservedQ
    · exact templateUnitClauses_outside_largerCounterNamespace
        hn kind reservedX reservedQ
  · exact insideRootForbiddenUnitClauses_outside_largerCounterNamespace
      hn reservedX reservedQ

theorem complementSourceAtoms_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    ∀ key, key ∈ complementKeys →
      ¬InSequentialNamespace
        (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
        (complementSourceAtom key) := by
  intro key hkey
  change key ∈ complementContexts.map (fun context =>
    complementKey context.1 context.2.1 context.2.2) at hkey
  obtain ⟨⟨a, q, x⟩, _hcontext, rfl⟩ := List.mem_map.mp hkey
  rw [complementSourceAtom_key]
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    reservedX reservedQ (by omega) (by omega)

theorem rowColorAtoms_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4)
    (a : FourVertex) (q : Fin 4) :
    InputsOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (ProfileDDegreeFlooredCNF.rowColorAtoms a q) := by
  intro atom hatom
  simp only [ProfileDDegreeFlooredCNF.rowColorAtoms,
    List.mem_map] at hatom
  obtain ⟨x, _hx, rfl⟩ := hatom
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    reservedX reservedQ (by omega) (by omega)

/-! ## Compact counter family -/

def compactContextInputs (a : FourVertex) (q : Fin 4)
    (phase : CounterPhase) : List Nat :=
  if phase = ProfileDDegreeFlooredCNF.upperPhase then
    ProfileDDegreeFlooredCNF.rowColorAtoms a q
  else compactLowerInputs a q

def compactCounterSpec (context : CounterContext) : CounterSpec where
  tag := compactCounterTag context.1 context.2.1 context.2.2
  bound := ProfileDDegreeFlooredCNF.contextBound
    context.2.1 context.2.2
  inputs := compactContextInputs
    context.1 context.2.1 context.2.2

def compactCounterSpecs : List CounterSpec :=
  ProfileDDegreeFlooredCNF.counterContexts.map compactCounterSpec

theorem compactCounterSpecs_length : compactCounterSpecs.length = 32 := by
  simp [compactCounterSpecs,
    ProfileDDegreeFlooredCNF.counterContexts_length]

theorem compactCounterSpecs_tags_nodup :
    (compactCounterSpecs.map CounterSpec.tag).Nodup := by
  unfold compactCounterSpecs
  rw [List.map_map]
  exact ProfileDDegreeFlooredCNF.counterContexts_nodup.map
    compactCounterTag_injective

/-! ## Explicit complement valuation and exact counts -/

noncomputable def complementValuation {kind : Kind}
    (ext : FourExtension kind) : Sat.Valuation :=
  ComplementAtomCNF.complementExtension
    complementNamespaceTag complementSourceAtom
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext))

theorem complementValuation_satisfies_rawFmla {kind : Kind}
    (ext : FourExtension kind) :
    (complementValuation ext).satisfies_fmla
      (ProfileDFourRowCNF.fmla kind) := by
  apply ComplementAtomCNF.complementExtension_satisfies_base
  · exact rawFmla_outside_largerCounterNamespace
      (n := 60) (by omega) kind
      complementNamespaceVertex complementNamespaceColor
  · exact ProfileDFourRowCNF.fourExtension_satisfies_fmla ext

theorem complementValuation_satisfies_definitions {kind : Kind}
    (ext : FourExtension kind) :
    (complementValuation ext).satisfies_fmla
      complementDefinitionClauses := by
  exact ComplementAtomCNF.complementExtension_satisfies_definitions
    complementNamespaceTag complementSourceAtom complementKeys
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
    (complementSourceAtoms_outside_largerCounterNamespace
      (n := 60) (by omega)
      complementNamespaceVertex complementNamespaceColor)

theorem trueInputCount_rowColorAtoms_complementValuation
    {kind : Kind} (ext : FourExtension kind)
    (a : FourVertex) (q : Fin 4) :
    trueInputCount (complementValuation ext)
        (ProfileDDegreeFlooredCNF.rowColorAtoms a q) =
      (rowColorSupport (ext.rows a) q).card := by
  calc
    trueInputCount (complementValuation ext)
        (ProfileDDegreeFlooredCNF.rowColorAtoms a q) =
      trueInputCount
        (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
        (ProfileDDegreeFlooredCNF.rowColorAtoms a q) :=
      SequentialAtMostManyCNF.trueInputCount_eq_of_agrees _ (by
        intro atom hatom
        exact ComplementAtomCNF.complementExtension_eq_of_outside
          complementNamespaceTag complementSourceAtom
          (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
          (rowColorAtoms_outside_largerCounterNamespace
            (n := 60) (by omega)
            complementNamespaceVertex complementNamespaceColor
            a q atom hatom))
    _ = (rowColorSupport (ext.rows a) q).card :=
      ProfileDDegreeFlooredCNF.trueInputCount_rowColorAtoms ext a q

/-- The 46 fresh lower inputs count exactly the complement of the selected
row support. -/
theorem trueInputCount_compactLowerInputs
    {kind : Kind} (ext : FourExtension kind)
    (a : FourVertex) (q : Fin 4) :
    trueInputCount (complementValuation ext)
        (compactLowerInputs a q) =
      46 - (rowColorSupport (ext.rows a) q).card := by
  unfold complementValuation
  rw [compactLowerInputs,
    ComplementAtomCNF.trueInputCount_complementAtoms,
    rowColorKeys_length, rowColorKeys_map_sourceAtom,
    ProfileDDegreeFlooredCNF.trueInputCount_rowColorAtoms]

/-! ## Exact standalone compact formula -/

def compactBaseFmla (kind : Kind) : Sat.Fmla :=
  ProfileDFourRowCNF.fmla kind ++ complementDefinitionClauses

def fmla (kind : Kind) : Sat.Fmla :=
  manySequentialAtMostFmla (compactBaseFmla kind) compactCounterSpecs

theorem compactCounterSpecs_wellFormed (kind : Kind) :
    ManyCounterWellFormed (compactBaseFmla kind) compactCounterSpecs := by
  refine ⟨compactCounterSpecs_tags_nodup, ?_, ?_⟩
  · intro reserved hreserved
    have hreserved' : reserved ∈ compactCounterSpecs := hreserved
    simp only [compactCounterSpecs, List.mem_map] at hreserved'
    obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hreserved'
    unfold compactBaseFmla
    apply ThresholdDegreeCapsCNF.formulaOutsideNamespace_append
    · exact rawFmla_outside_largerCounterNamespace
        (n := 61) (by omega) kind (compactNamespaceVertex a phase) q
    · exact ComplementAtomCNF.complementDefinitionClauses_outside_otherNamespace
        (complementNamespaceTag_ne_compactCounterTag a q phase)
        complementSourceAtom complementKeys
        (complementSourceAtoms_outside_largerCounterNamespace
          (n := 61) (by omega) (compactNamespaceVertex a phase) q)
  · intro reserved hreserved target htarget
    have hreserved' : reserved ∈ compactCounterSpecs := hreserved
    have htarget' : target ∈ compactCounterSpecs := htarget
    simp only [compactCounterSpecs, List.mem_map] at hreserved' htarget'
    obtain ⟨⟨reservedA, reservedQ, reservedPhase⟩,
      _hreservedContext, rfl⟩ := hreserved'
    obtain ⟨⟨targetA, targetQ, targetPhase⟩,
      _htargetContext, rfl⟩ := htarget'
    unfold compactCounterSpec
    change InputsOutsideNamespace
      (compactCounterTag reservedA reservedQ reservedPhase)
      (compactContextInputs targetA targetQ targetPhase)
    unfold compactContextInputs
    split
    · exact rowColorAtoms_outside_largerCounterNamespace
        (n := 61) (by omega)
        (compactNamespaceVertex reservedA reservedPhase) reservedQ
        targetA targetQ
    · exact ComplementAtomCNF.complementAtoms_outside_otherNamespace
        (complementNamespaceTag_ne_compactCounterTag
          reservedA reservedQ reservedPhase)
        (rowColorKeys targetA targetQ)

theorem allCaps_of_degreeFlooredFourExtension {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    AllCaps compactCounterSpecs
      (complementValuation ext.toFourExtension) := by
  intro spec hspec
  have hspec' : spec ∈ compactCounterSpecs := hspec
  simp only [compactCounterSpecs, List.mem_map] at hspec'
  obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hspec'
  unfold InputsAtMost compactCounterSpec
  change trueInputCount (complementValuation ext.toFourExtension)
      (compactContextInputs a q phase) ≤
    ProfileDDegreeFlooredCNF.contextBound q phase
  by_cases hphase : phase = ProfileDDegreeFlooredCNF.upperPhase
  · simp only [compactContextInputs,
      ProfileDDegreeFlooredCNF.contextBound, hphase, ↓reduceIte]
    rw [trueInputCount_rowColorAtoms_complementValuation]
    by_cases hq : q = 0
    · subst q
      simpa [ProfileDDegreeFlooredCNF.supportUpperBound] using
        ext.zeroSupportUpper a
    · simpa [ProfileDDegreeFlooredCNF.supportUpperBound, hq] using
        ext.nonzeroSupportUpper a q hq
  · simp only [compactContextInputs,
      ProfileDDegreeFlooredCNF.contextBound, hphase, ↓reduceIte]
    rw [trueInputCount_compactLowerInputs]
    by_cases hq : q = 0
    · subst q
      have hlower := ext.zeroSupportLower a
      simp only [ProfileDDegreeFlooredCNF.complementaryUpperBound,
        ↓reduceIte]
      omega
    · have hlower := ext.nonzeroSupportLower a q hq
      simp only [ProfileDDegreeFlooredCNF.complementaryUpperBound,
        hq, ↓reduceIte]
      omega

theorem degreeFlooredFourExtension_satisfies_fmla {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    (iteratedSequentialExtension compactCounterSpecs
      (complementValuation ext.toFourExtension)).satisfies_fmla
        (fmla kind) := by
  apply iteratedExtension_satisfies_manySequentialAtMostFmla
    (compactBaseFmla kind) compactCounterSpecs
    (complementValuation ext.toFourExtension)
    (compactCounterSpecs_wellFormed kind)
  · constructor
    intro clause hclause
    rcases List.mem_append.mp hclause with hraw | hdefinitions
    · exact (complementValuation_satisfies_rawFmla
        ext.toFourExtension).prop clause hraw
    · exact (complementValuation_satisfies_definitions
        ext.toFourExtension).prop clause hdefinitions
  · exact allCaps_of_degreeFlooredFourExtension ext

theorem noDegreeFlooredFourExtension_of_lrat (kind : Kind)
    (hunsat : (fmla kind).proof []) :
    ¬Nonempty (DegreeFlooredFourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat _ (degreeFlooredFourExtension_satisfies_fmla ext)

/-! ## Independently verified compact clause counts -/

def contextCounterClauseCount (q : Fin 4) (phase : CounterPhase) : Nat :=
  if phase = ProfileDDegreeFlooredCNF.upperPhase then
    if q = 0 then 1442 else 1262
  else if q = 0 then 3242 else 3602

theorem counterBlock_compactCounterSpec_length (context : CounterContext) :
    (counterBlock (compactCounterSpec context)).length =
      contextCounterClauseCount context.2.1 context.2.2 := by
  rcases context with ⟨a, q, phase⟩
  unfold counterBlock compactCounterSpec
  rw [SequentialAtMostCNF.sequentialAtMostFmla_length]
  fin_cases q <;> fin_cases phase <;>
    simp [contextCounterClauseCount, compactContextInputs,
      ProfileDDegreeFlooredCNF.contextBound,
      ProfileDDegreeFlooredCNF.supportUpperBound,
      ProfileDDegreeFlooredCNF.complementaryUpperBound,
      ProfileDDegreeFlooredCNF.upperPhase,
      ProfileDDegreeFlooredCNF.rowColorAtoms_length,
      compactLowerInputs_length]

theorem compactCounterClauseContribution :
    ((compactCounterSpecs.map fun spec =>
      (counterBlock spec).length).sum) = 77104 := by
  rw [compactCounterSpecs, List.map_map]
  change ((ProfileDDegreeFlooredCNF.counterContexts.map fun context =>
    (counterBlock (compactCounterSpec context)).length).sum) = 77104
  simp only [counterBlock_compactCounterSpec_length]
  unfold ProfileDDegreeFlooredCNF.counterContexts
  decide

theorem rawFmla_length (kind : Kind) :
    (ProfileDFourRowCNF.fmla kind).length = 87311 := by
  have hgood : (goodColoringFmla 50 4).length = 86975 := by decide
  simp [ProfileDFourRowCNF.fmla, hgood,
    ProfileDFourRowCNF.templateUnitClauses_length,
    ProfileDFourRowCNF.insideRootForbiddenUnitClauses_length]

theorem compactBaseFmla_length (kind : Kind) :
    (compactBaseFmla kind).length = 88783 := by
  simp [compactBaseFmla, rawFmla_length,
    complementDefinitionClauses_length]

/-- Exact total: 87,311 raw clauses, 1,472 complement definitions, and
77,104 compact counter clauses. -/
theorem fmla_length (kind : Kind) : (fmla kind).length = 165887 := by
  rw [fmla, manySequentialAtMostFmla_length,
    compactBaseFmla_length, compactCounterClauseContribution]

/-! ## Six standalone representative endpoints -/

structure RepresentativeLRATRefutations : Prop where
  uuu : (fmla .uuu).proof []
  uut : (fmla .uut).proof []
  utu : (fmla .utu).proof []
  utt : (fmla .utt).proof []
  ttu : (fmla .ttu).proof []
  ttt : (fmla .ttt).proof []

theorem RepresentativeLRATRefutations.obstructions
    (h : RepresentativeLRATRefutations) :
    SwapRepresentativeDegreeFlooredObstructions where
  uuu := noDegreeFlooredFourExtension_of_lrat .uuu h.uuu
  uut := noDegreeFlooredFourExtension_of_lrat .uut h.uut
  utu := noDegreeFlooredFourExtension_of_lrat .utu h.utu
  utt := noDegreeFlooredFourExtension_of_lrat .utt h.utt
  ttu := noDegreeFlooredFourExtension_of_lrat .ttu h.ttu
  ttt := noDegreeFlooredFourExtension_of_lrat .ttt h.ttt

theorem no_profileD_star_of_compactDegreeFloored_lrat
    (h : RepresentativeLRATRefutations) :
    ¬Nonempty (SingleRootStarCNF.CanonicalStarWitness ProfileD) :=
  no_profileD_star_of_swapRepresentativeDegreeFlooredObstructions
    h.obstructions

/-! ## Bidirectional profile-C-conditional completion cuts -/

/-- For every vertex of the second K15, some edge into the first K15 has
the first block's omitted host colour, namely colour one. -/
def secondVertexHitsFirstK15Clause (source : Fin 15) : Sat.Clause :=
  (List.finRange 15).map fun target =>
    Sat.Literal.pos (edgeAtom
      (4 + target.val) (19 + source.val) 1)

def secondVerticesHitFirstK15Clauses : Sat.Fmla :=
  (List.finRange 15).map secondVertexHitsFirstK15Clause

theorem secondVertexHitsFirstK15Clause_length (source : Fin 15) :
    (secondVertexHitsFirstK15Clause source).length = 15 := by
  simp [secondVertexHitsFirstK15Clause]

theorem secondVerticesHitFirstK15Clauses_length :
    secondVerticesHitFirstK15Clauses.length = 15 := by
  simp [secondVerticesHitFirstK15Clauses]

/-- Both orientations are valid simultaneously for each D object. -/
def bidirectionalCompletionClauses : Sat.Fmla :=
  ProfileDConditionalCompletionCNF.firstVerticesHitSecondK15Clauses ++
    secondVerticesHitFirstK15Clauses

theorem bidirectionalCompletionClauses_length :
    bidirectionalCompletionClauses.length = 30 := by
  simp [bidirectionalCompletionClauses,
    ProfileDConditionalCompletionCNF.firstVerticesHitSecondK15Clauses_length,
    secondVerticesHitFirstK15Clauses_length]

private theorem firstVertex_has_blocking_edge
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) (source : Fin 15) :
    ∃ target : Fin 15,
      ext.tail.coloring
          (blockVertex 0 source.val) (blockVertex 1 target.val) = 2 := by
  have hnotCompletion :
      ¬ProfileDToCCompletionTransfer.CompletesSecondK15 ext source := by
    intro hcompletion
    exact hC (ProfileDToCCompletionTransfer.toCKind kind)
      ⟨ProfileDToCCompletionTransfer.transferWith
        ext source hcompletion⟩
  by_contra hnone
  apply hnotCompletion
  apply (ProfileDToCCompletionTransfer.completesSecondK15_iff_avoids
    ext source).2
  intro target hcolour
  apply hnone
  exact ⟨target, hcolour⟩

/-- Apply the equal-K15 block/host-colour transport before the existing
completion transfer.  Pulling the resulting colour-two edge back swaps its
orientation and turns it into a colour-one edge. -/
theorem secondVertex_has_blocking_edge
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) (source : Fin 15) :
    ∃ target : Fin 15,
      ext.tail.coloring
          (blockVertex 0 target.val) (blockVertex 1 source.val) = 1 := by
  let transported :=
    ProfileDFourRowKindSymmetry.transportFourExtension ext
  let transportedSource : Fin 15 :=
    (ProfileDFourRowKindSymmetry.localK15Zero kind).symm source
  obtain ⟨transportedTarget, htarget⟩ :=
    firstVertex_has_blocking_edge hC transported transportedSource
  let target : Fin 15 :=
    ProfileDFourRowKindSymmetry.localK15One kind transportedTarget
  refine ⟨target, ?_⟩
  change ProfileDFourRowKindSymmetry.hostColorPerm
      (ext.tail.coloring
        (ProfileDFourRowKindSymmetry.tailVertexPerm kind
          (blockVertex 0 transportedSource.val))
        (ProfileDFourRowKindSymmetry.tailVertexPerm kind
          (blockVertex 1 transportedTarget.val))) = 2 at htarget
  rw [ProfileDFourRowKindSymmetry.tailVertexPerm_blockZero,
    ProfileDFourRowKindSymmetry.tailVertexPerm_blockOne] at htarget
  have hsource :
      ProfileDFourRowKindSymmetry.localK15Zero kind transportedSource =
        source := by
    simp [transportedSource]
  rw [hsource] at htarget
  rw [ext.tail.coloring.color_symm]
  apply ProfileDFourRowKindSymmetry.hostColorPerm.injective
  rw [htarget]
  have hone :
      ProfileDFourRowKindSymmetry.hostColorPerm (1 : Fin 4) = 2 := by
    simpa using
      (ProfileDFourRowKindSymmetry.hostColorPerm_succ_apply (1 : Fin 3))
  exact hone.symm

theorem satisfies_secondVertexHitsFirstK15Clause
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) (source : Fin 15) :
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)).satisfies
        (secondVertexHitsFirstK15Clause source) := by
  obtain ⟨target, htarget⟩ :=
    secondVertex_has_blocking_edge hC ext source
  let leftTail : TailVertex := blockVertex 0 target.val
  let rightTail : TailVertex := blockVertex 1 source.val
  let left : ProfileDFourRowCNF.TotalVertex :=
    ProfileDFourRowCNF.tailVertex leftTail
  let right : ProfileDFourRowCNF.TotalVertex :=
    ProfileDFourRowCNF.tailVertex rightTail
  let one : Fin 4 := 1
  have hleftTail : leftTail.val = target.val := by
    simp [leftTail, blockVertex_val 0 target.isLt, blockStart]
  have hrightTail : rightTail.val = 15 + source.val := by
    simp [rightTail, blockVertex_val 1 source.isLt, blockStart]
  have hleft : left.val = 4 + target.val := by
    simp [left, ProfileDFourRowCNF.tailVertex, hleftTail]
  have hright : right.val = 19 + source.val := by
    simp [right, ProfileDFourRowCNF.tailVertex, hrightTail]
    omega
  apply satisfies_of_mem_holds
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
    (l := Sat.Literal.pos
      (edgeAtom (4 + target.val) (19 + source.val) one.val))
  · unfold secondVertexHitsFirstK15Clause
    apply List.mem_map.mpr
    exact ⟨target, by simp, rfl⟩
  · change coloringValuation (ProfileDFourRowCNF.totalColoring ext)
      (edgeAtom (4 + target.val) (19 + source.val) one.val)
    have hatom :
        edgeAtom (4 + target.val) (19 + source.val) one.val =
          edgeAtom left right one := by
      simp [hleft, hright]
    rw [hatom, coloringValuation_edgeAtom]
    change ProfileDFourRowCNF.totalColoring ext
        (ProfileDFourRowCNF.tailVertex leftTail)
        (ProfileDFourRowCNF.tailVertex rightTail) = one
    rw [ProfileDFourRowCNF.totalColoring_tail_tail]
    simpa [leftTail, rightTail, one] using htarget

theorem satisfies_secondVerticesHitFirstK15Clauses
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)).satisfies_fmla
        secondVerticesHitFirstK15Clauses := by
  constructor
  intro clause hclause
  change clause ∈ (List.finRange 15).map
    secondVertexHitsFirstK15Clause at hclause
  obtain ⟨source, _hsource, rfl⟩ := List.mem_map.mp hclause
  exact satisfies_secondVertexHitsFirstK15Clause hC ext source

theorem satisfies_bidirectionalCompletionClauses
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)).satisfies_fmla
        bidirectionalCompletionClauses := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hforward | hreverse
  · exact
      (ProfileDConditionalCompletionCNF.satisfies_firstVerticesHitSecondK15Clauses
        hC ext).prop
        clause hforward
  · exact (satisfies_secondVerticesHitFirstK15Clauses hC ext).prop
      clause hreverse

/-! ## Raw bidirectional conditional profile D

This is the certificate target needed by the hierarchical C-first route.
It deliberately has no degree-floor or complement-counter layer: the six
representative refutations obstruct ordinary `FourExtension`s and therefore
recover the universal raw profile-D obstruction used by the B/A transfers. -/

/-- The ordinary 87,311-clause D formula strengthened by both simultaneous
15-clause completion orientations. -/
def rawBidirectionalConditionalFmla (kind : Kind) : Sat.Fmla :=
  ProfileDFourRowCNF.fmla kind ++ bidirectionalCompletionClauses

theorem fourExtension_satisfies_rawBidirectionalConditionalFmla
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (coloringValuation
      (ProfileDFourRowCNF.totalColoring ext)).satisfies_fmla
        (rawBidirectionalConditionalFmla kind) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hraw | hcompletion
  · exact (ProfileDFourRowCNF.fourExtension_satisfies_fmla ext).prop
      clause hraw
  · exact (satisfies_bidirectionalCompletionClauses hC ext).prop
      clause hcompletion

theorem noFourExtension_of_C_obstruction_rawBidirectional_lrat
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (kind : Kind)
    (hunsat : (rawBidirectionalConditionalFmla kind).proof []) :
    ¬Nonempty (FourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat
    (coloringValuation (ProfileDFourRowCNF.totalColoring ext))
    (fourExtension_satisfies_rawBidirectionalConditionalFmla hC ext)

theorem rawBidirectionalConditionalFmla_length (kind : Kind) :
    (rawBidirectionalConditionalFmla kind).length = 87341 := by
  simp [rawBidirectionalConditionalFmla, rawFmla_length,
    bidirectionalCompletionClauses_length]

/-- Six raw checked targets, one for each orbit under interchange of D's two
equal K15 blocks.  This structure contains no asserted certificate. -/
structure RawBidirectionalConditionalRepresentativeLRATRefutations : Prop where
  uuu : (rawBidirectionalConditionalFmla .uuu).proof []
  uut : (rawBidirectionalConditionalFmla .uut).proof []
  utu : (rawBidirectionalConditionalFmla .utu).proof []
  utt : (rawBidirectionalConditionalFmla .utt).proof []
  ttu : (rawBidirectionalConditionalFmla .ttu).proof []
  ttt : (rawBidirectionalConditionalFmla .ttt).proof []

theorem RawBidirectionalConditionalRepresentativeLRATRefutations.obstructions
    (h : RawBidirectionalConditionalRepresentativeLRATRefutations)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction) :
    ProfileDFourRowKindSymmetry.SwapRepresentativeObstructions where
  uuu := noFourExtension_of_C_obstruction_rawBidirectional_lrat
    hC .uuu h.uuu
  uut := noFourExtension_of_C_obstruction_rawBidirectional_lrat
    hC .uut h.uut
  utu := noFourExtension_of_C_obstruction_rawBidirectional_lrat
    hC .utu h.utu
  utt := noFourExtension_of_C_obstruction_rawBidirectional_lrat
    hC .utt h.utt
  ttu := noFourExtension_of_C_obstruction_rawBidirectional_lrat
    hC .ttu h.ttu
  ttt := noFourExtension_of_C_obstruction_rawBidirectional_lrat
    hC .ttt h.ttt

theorem RawBidirectionalConditionalRepresentativeLRATRefutations.universalFourRowObstruction
    (h : RawBidirectionalConditionalRepresentativeLRATRefutations)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction) :
    ProfileDFourRowBoundary.UniversalFourRowObstruction :=
  (h.obstructions hC).universalFourRowObstruction

theorem no_profileD_star_of_rawBidirectionalConditional_lrat
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (h : RawBidirectionalConditionalRepresentativeLRATRefutations) :
    ¬Nonempty (SingleRootStarCNF.CanonicalStarWitness ProfileD) :=
  no_profileD_star_of_universalFourRowObstruction
    (h.universalFourRowObstruction hC)

theorem bidirectionalCompletionClauses_outside_largerCounterNamespace
    {n : Nat} (hn : 50 ≤ n) (reservedX : Fin n) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      bidirectionalCompletionClauses := by
  intro clause hclause literal hliteral
  rcases List.mem_append.mp hclause with hforward | hreverse
  · change clause ∈ (List.finRange 15).map
      ProfileDConditionalCompletionCNF.firstVertexHitsSecondK15Clause
        at hforward
    obtain ⟨source, _hsource, rfl⟩ := List.mem_map.mp hforward
    change literal ∈ (List.finRange 15).map fun target =>
      Sat.Literal.pos
        (edgeAtom (4 + source.val) (19 + target.val) 2) at hliteral
    obtain ⟨target, _htarget, rfl⟩ := List.mem_map.mp hliteral
    exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
      reservedX reservedQ (by omega) (by omega)
  · change clause ∈ (List.finRange 15).map
      secondVertexHitsFirstK15Clause at hreverse
    obtain ⟨source, _hsource, rfl⟩ := List.mem_map.mp hreverse
    change literal ∈ (List.finRange 15).map fun target =>
      Sat.Literal.pos
        (edgeAtom (4 + target.val) (19 + source.val) 1) at hliteral
    obtain ⟨target, _htarget, rfl⟩ := List.mem_map.mp hliteral
    exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
      reservedX reservedQ (by omega) (by omega)

/-- The complement valuation preserves the 30 edge-only conditional cuts. -/
theorem complementValuation_satisfies_bidirectionalCompletionClauses
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : FourExtension kind) :
    (complementValuation ext).satisfies_fmla
      bidirectionalCompletionClauses := by
  apply ComplementAtomCNF.complementExtension_satisfies_base
  · exact bidirectionalCompletionClauses_outside_largerCounterNamespace
      (n := 60) (by omega)
      complementNamespaceVertex complementNamespaceColor
  · exact satisfies_bidirectionalCompletionClauses hC ext

def conditionalCompactBaseFmla (kind : Kind) : Sat.Fmla :=
  compactBaseFmla kind ++ bidirectionalCompletionClauses

def conditionalFmla (kind : Kind) : Sat.Fmla :=
  manySequentialAtMostFmla
    (conditionalCompactBaseFmla kind) compactCounterSpecs

theorem conditionalCompactCounterSpecs_wellFormed (kind : Kind) :
    ManyCounterWellFormed
      (conditionalCompactBaseFmla kind) compactCounterSpecs := by
  let hcompact := compactCounterSpecs_wellFormed kind
  refine ⟨hcompact.tags_nodup, ?_, ?_⟩
  · intro reserved hreserved
    unfold conditionalCompactBaseFmla
    apply ThresholdDegreeCapsCNF.formulaOutsideNamespace_append
    · exact hcompact.base_outside reserved hreserved
    · have hreserved' : reserved ∈ compactCounterSpecs := hreserved
      simp only [compactCounterSpecs, List.mem_map] at hreserved'
      obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hreserved'
      exact bidirectionalCompletionClauses_outside_largerCounterNamespace
        (n := 61) (by omega) (compactNamespaceVertex a phase) q
  · intro reserved hreserved target htarget
    exact hcompact.inputs_outside reserved hreserved target htarget

theorem conditionalDegreeFlooredFourExtension_satisfies_fmla
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    {kind : Kind} (ext : DegreeFlooredFourExtension kind) :
    (iteratedSequentialExtension compactCounterSpecs
      (complementValuation ext.toFourExtension)).satisfies_fmla
        (conditionalFmla kind) := by
  apply iteratedExtension_satisfies_manySequentialAtMostFmla
    (conditionalCompactBaseFmla kind) compactCounterSpecs
    (complementValuation ext.toFourExtension)
    (conditionalCompactCounterSpecs_wellFormed kind)
  · constructor
    intro clause hclause
    rcases List.mem_append.mp hclause with hcompact | hcompletion
    · rcases List.mem_append.mp hcompact with hraw | hdefinitions
      · exact (complementValuation_satisfies_rawFmla
          ext.toFourExtension).prop clause hraw
      · exact (complementValuation_satisfies_definitions
          ext.toFourExtension).prop clause hdefinitions
    · exact
        (complementValuation_satisfies_bidirectionalCompletionClauses
          hC ext.toFourExtension).prop clause hcompletion
  · exact allCaps_of_degreeFlooredFourExtension ext

theorem noDegreeFlooredFourExtension_of_C_obstruction_compact_lrat
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (kind : Kind) (hunsat : (conditionalFmla kind).proof []) :
    ¬Nonempty (DegreeFlooredFourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat _
    (conditionalDegreeFlooredFourExtension_satisfies_fmla hC ext)

theorem conditionalCompactBaseFmla_length (kind : Kind) :
    (conditionalCompactBaseFmla kind).length = 88813 := by
  simp [conditionalCompactBaseFmla, compactBaseFmla_length,
    bidirectionalCompletionClauses_length]

/-- With both simultaneous orientations the conditional total is 165,917,
fifteen clauses above the earlier one-orientation estimate 165,902. -/
theorem conditionalFmla_length (kind : Kind) :
    (conditionalFmla kind).length = 165917 := by
  rw [conditionalFmla, manySequentialAtMostFmla_length,
    conditionalCompactBaseFmla_length, compactCounterClauseContribution]

structure ConditionalRepresentativeLRATRefutations : Prop where
  uuu : (conditionalFmla .uuu).proof []
  uut : (conditionalFmla .uut).proof []
  utu : (conditionalFmla .utu).proof []
  utt : (conditionalFmla .utt).proof []
  ttu : (conditionalFmla .ttu).proof []
  ttt : (conditionalFmla .ttt).proof []

theorem ConditionalRepresentativeLRATRefutations.obstructions
    (h : ConditionalRepresentativeLRATRefutations)
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction) :
    SwapRepresentativeDegreeFlooredObstructions where
  uuu := noDegreeFlooredFourExtension_of_C_obstruction_compact_lrat
    hC .uuu h.uuu
  uut := noDegreeFlooredFourExtension_of_C_obstruction_compact_lrat
    hC .uut h.uut
  utu := noDegreeFlooredFourExtension_of_C_obstruction_compact_lrat
    hC .utu h.utu
  utt := noDegreeFlooredFourExtension_of_C_obstruction_compact_lrat
    hC .utt h.utt
  ttu := noDegreeFlooredFourExtension_of_C_obstruction_compact_lrat
    hC .ttu h.ttu
  ttt := noDegreeFlooredFourExtension_of_C_obstruction_compact_lrat
    hC .ttt h.ttt

theorem no_profileD_star_of_conditionalCompactDegreeFloored_lrat
    (hC : ProfileCFourRowBoundary.UniversalFourRowObstruction)
    (h : ConditionalRepresentativeLRATRefutations) :
    ¬Nonempty (SingleRootStarCNF.CanonicalStarWitness ProfileD) :=
  no_profileD_star_of_swapRepresentativeDegreeFlooredObstructions
    (h.obstructions hC)

#print axioms R4333.ProfileDCompactDegreeFlooredCNF.complementValuation_satisfies_definitions
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.trueInputCount_compactLowerInputs
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.compactCounterSpecs_wellFormed
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.degreeFlooredFourExtension_satisfies_fmla
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.compactCounterClauseContribution
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.fmla_length
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.RepresentativeLRATRefutations.obstructions
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.no_profileD_star_of_compactDegreeFloored_lrat
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.secondVertex_has_blocking_edge
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.satisfies_bidirectionalCompletionClauses
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.fourExtension_satisfies_rawBidirectionalConditionalFmla
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.noFourExtension_of_C_obstruction_rawBidirectional_lrat
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.rawBidirectionalConditionalFmla_length
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.RawBidirectionalConditionalRepresentativeLRATRefutations.obstructions
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.RawBidirectionalConditionalRepresentativeLRATRefutations.universalFourRowObstruction
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.no_profileD_star_of_rawBidirectionalConditional_lrat
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.conditionalCompactCounterSpecs_wellFormed
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.conditionalDegreeFlooredFourExtension_satisfies_fmla
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.conditionalFmla_length
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.ConditionalRepresentativeLRATRefutations.obstructions
#print axioms R4333.ProfileDCompactDegreeFlooredCNF.no_profileD_star_of_conditionalCompactDegreeFloored_lrat

end ProfileDCompactDegreeFlooredCNF
end R4333
