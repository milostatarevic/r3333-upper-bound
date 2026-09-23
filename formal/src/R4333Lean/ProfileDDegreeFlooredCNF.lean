import R4333Lean.ProfileDRowSupportBounds61
import R4333Lean.ProfileDThresholdCappedCNF
import R4333Lean.SequentialAtMostManyCNF

/-!
# Exact degree-floored profile-D formulas

For each of the four selected profile-D rows, the full canonical `K_61`
star proves the following support intervals into the 46-vertex tail:

* colour zero has support in `[11, 15]`;
* each nonzero colour has support in `[7, 13]`.

This file appends exactly 32 sequential counters to the ordinary profile-D
four-row formula: an upper and a lower counter for each row/colour pair.
Upper bounds count the 46 atoms of that colour directly.  Lower bounds use
the one-hot base encoding and count the 138 atoms in the other three
colours, giving bounds 35 and 39 respectively.

All clause order, input order, bounds, and auxiliary namespaces are Lean
definitions.  The six swap-representative checked-refutation fields are only
an interface; no certificate inhabitant is supplied here.
-/

namespace R4333
namespace ProfileDDegreeFlooredCNF

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDFourRowCNF
open ProfileDRowSupportBounds61

set_option maxRecDepth 1000000

abbrev CounterPhase := Fin 2
abbrev CounterContext := FourVertex × (Fin 4 × CounterPhase)

/-- Phase zero is the direct upper counter; phase one is the complementary
counter which expresses the lower bound. -/
def upperPhase : CounterPhase := 0

def lowerPhase : CounterPhase := 1

/-- Four rows, then four colours, then upper/lower, all in `Fin` order. -/
def counterContexts : List CounterContext :=
  (List.finRange 4).product
    ((List.finRange 4).product (List.finRange 2))

theorem counterContexts_length : counterContexts.length = 32 := by
  calc
    counterContexts.length =
        (List.finRange 4).length *
          ((List.finRange 4).product (List.finRange 2)).length :=
      List.length_product _ _
    _ = (List.finRange 4).length *
        ((List.finRange 4).length * (List.finRange 2).length) := by
      exact congrArg (fun n => (List.finRange 4).length * n)
        (List.length_product (List.finRange 4) (List.finRange 2))
    _ = 32 := by simp

theorem counterContexts_nodup : counterContexts.Nodup := by
  exact (List.nodup_finRange 4).product
    ((List.nodup_finRange 4).product (List.nodup_finRange 2))

/-- Eight synthetic vertices encode `(selected row, phase)`.  Feeding this
vertex and the selected colour to the standard `K_50` degree-counter tag
gives 32 distinct tags, all above every base edge namespace. -/
def namespaceVertex (a : FourVertex) (phase : CounterPhase) : Fin 50 :=
  ⟨a.val * 2 + phase.val, by omega⟩

theorem namespaceVertex_injective :
    Function.Injective
      (fun ap : FourVertex × CounterPhase => namespaceVertex ap.1 ap.2) := by
  decide

/-- The exact auxiliary tag for one row/colour/phase context. -/
def counterTag (a : FourVertex) (q : Fin 4)
    (phase : CounterPhase) : Nat :=
  OutsideDegreeCapCNF.outsideDegreeCounterTag
    (namespaceVertex a phase) q

theorem counterTag_injective :
    Function.Injective (fun context : CounterContext =>
      counterTag context.1 context.2.1 context.2.2) := by
  rintro ⟨a, q, phase⟩ ⟨b, r, otherPhase⟩ h
  obtain ⟨hvertex, hcolor⟩ :=
    OutsideDegreeCapCNF.outsideDegreeCounterTag_injective h
  have hap : (a, phase) = (b, otherPhase) :=
    namespaceVertex_injective hvertex
  cases hap
  cases hcolor
  rfl

/-! ## Exact counter inputs -/

/-- The 46 row-tail atoms of one selected colour, in tail-vertex order. -/
def rowColorAtoms (a : FourVertex) (q : Fin 4) : List Nat :=
  (List.finRange 46).map fun x : Fin 46 =>
    FiniteColorCNF.edgeAtom a.val (4 + x.val) q.val

theorem rowColorAtoms_length (a : FourVertex) (q : Fin 4) :
    (rowColorAtoms a q).length = 46 := by
  simp [rowColorAtoms]

/-- The other three colours in their inherited `Fin 4` order. -/
def otherColors (q : Fin 4) : List (Fin 4) :=
  (List.finRange 4).filter fun r => r ≠ q

theorem otherColors_length (q : Fin 4) : (otherColors q).length = 3 := by
  fin_cases q <;> decide

@[simp] theorem otherColors_zero :
    otherColors (0 : Fin 4) = [1, 2, 3] := by decide

@[simp] theorem otherColors_one :
    otherColors (1 : Fin 4) = [0, 2, 3] := by decide

@[simp] theorem otherColors_two :
    otherColors (2 : Fin 4) = [0, 1, 3] := by decide

@[simp] theorem otherColors_three :
    otherColors (3 : Fin 4) = [0, 1, 2] := by decide

/-- Lower-bound inputs: colour-major order over the three colours other
than `q`, with the 46 tail coordinates in order inside each colour. -/
def rowOtherColorAtoms (a : FourVertex) (q : Fin 4) : List Nat :=
  (otherColors q).flatMap fun r => rowColorAtoms a r

theorem rowOtherColorAtoms_length (a : FourVertex) (q : Fin 4) :
    (rowOtherColorAtoms a q).length = 138 := by
  rw [rowOtherColorAtoms, List.length_flatMap]
  simp [rowColorAtoms_length, otherColors_length]

/-- Direct upper bound for one colour. -/
def supportUpperBound (q : Fin 4) : Nat :=
  if q = 0 then 15 else 13

/-- Bound on the other-colour count equivalent to the support lower bound:
`46 - 11 = 35` for zero, and `46 - 7 = 39` otherwise. -/
def complementaryUpperBound (q : Fin 4) : Nat :=
  if q = 0 then 35 else 39

def contextBound (q : Fin 4) (phase : CounterPhase) : Nat :=
  if phase = upperPhase then supportUpperBound q
  else complementaryUpperBound q

def contextInputs (a : FourVertex) (q : Fin 4)
    (phase : CounterPhase) : List Nat :=
  if phase = upperPhase then rowColorAtoms a q
  else rowOtherColorAtoms a q

/-- One authoritative sequential-counter specification. -/
def counterSpec (context : CounterContext) : CounterSpec where
  tag := counterTag context.1 context.2.1 context.2.2
  bound := contextBound context.2.1 context.2.2
  inputs := contextInputs context.1 context.2.1 context.2.2

/-- The exact 32-counter list. -/
def counterSpecs : List CounterSpec :=
  counterContexts.map counterSpec

theorem counterSpecs_length : counterSpecs.length = 32 := by
  simp [counterSpecs, counterContexts_length]

theorem counterSpecs_tags_nodup :
    (counterSpecs.map CounterSpec.tag).Nodup := by
  unfold counterSpecs
  rw [List.map_map]
  exact counterContexts_nodup.map counterTag_injective

/-! ## Exact true-input semantics -/

@[simp] theorem totalColoring_free_tail {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (x : TailVertex) :
    totalColoring ext (freeVertex a) (tailVertex x) = ext.rows a x := by
  simp [totalColoring, pullbackColoring]

private theorem count_finRange_eq_rowColorSupport
    (row : TailVertex → Fin 4) (q : Fin 4) :
    List.countP (fun x : TailVertex => decide (row x = q))
        (List.finRange 46) =
      (rowColorSupport row q).card := by
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup
    ((List.nodup_finRange 46).filter _)]
  congr 1
  ext x
  simp [rowColorSupport]

/-- A direct input list counts exactly the selected row's support in `q`. -/
theorem trueInputCount_rowColorAtoms {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (q : Fin 4) :
    trueInputCount (coloringValuation (totalColoring ext))
        (rowColorAtoms a q) =
      (rowColorSupport (ext.rows a) q).card := by
  unfold trueInputCount rowColorAtoms
  rw [List.countP_map]
  have hbits :
      (truthBit (coloringValuation (totalColoring ext)) ∘
          fun x : TailVertex =>
            FiniteColorCNF.edgeAtom a.val (4 + x.val) q.val) =
        (fun x : TailVertex => decide (ext.rows a x = q)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply]
    rw [truthBit_eq_true]
    simp only [decide_eq_true_eq]
    change coloringValuation (totalColoring ext)
        (FiniteColorCNF.edgeAtom
          (freeVertex a).val (tailVertex x).val q.val) ↔
      ext.rows a x = q
    rw [coloringValuation_edgeAtom]
    simp
  rw [hbits]
  exact count_finRange_eq_rowColorSupport (ext.rows a) q

private theorem trueInputCount_flatMap
    (v : Sat.Valuation) {A : Type*} (contexts : List A)
    (inputs : A → List Nat) :
    trueInputCount v (contexts.flatMap inputs) =
      (contexts.map fun context => trueInputCount v (inputs context)).sum := by
  simp [trueInputCount, List.countP_flatMap, Function.comp_def]

/-- By the one-hot colouring valuation, the complementary input list counts
exactly all 46 row positions not coloured `q`. -/
theorem trueInputCount_rowOtherColorAtoms {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (q : Fin 4) :
    trueInputCount (coloringValuation (totalColoring ext))
        (rowOtherColorAtoms a q) =
      46 - (rowColorSupport (ext.rows a) q).card := by
  have hsum := ProfileDRowSupportBounds61.rowColorSupport_sum_fin4
    (ext.rows a)
  simp only [TailVertex, Fintype.card_fin] at hsum
  rw [rowOtherColorAtoms, trueInputCount_flatMap]
  fin_cases q <;>
    simp [trueInputCount_rowColorAtoms] <;> omega

/-! ## Collision-free 32-counter namespace -/

theorem rowColorAtoms_outside_counterNamespace
    (reservedA : FourVertex) (reservedQ : Fin 4)
    (reservedPhase : CounterPhase)
    (targetA : FourVertex) (targetQ : Fin 4) :
    InputsOutsideNamespace
      (counterTag reservedA reservedQ reservedPhase)
      (rowColorAtoms targetA targetQ) := by
  intro atom hatom
  simp only [rowColorAtoms, List.mem_map] at hatom
  obtain ⟨x, _hx, rfl⟩ := hatom
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    (namespaceVertex reservedA reservedPhase) reservedQ
    (by omega) (by omega)

theorem rowOtherColorAtoms_outside_counterNamespace
    (reservedA : FourVertex) (reservedQ : Fin 4)
    (reservedPhase : CounterPhase)
    (targetA : FourVertex) (targetQ : Fin 4) :
    InputsOutsideNamespace
      (counterTag reservedA reservedQ reservedPhase)
      (rowOtherColorAtoms targetA targetQ) := by
  intro atom hatom
  simp only [rowOtherColorAtoms, List.mem_flatMap] at hatom
  obtain ⟨r, _hr, hatom⟩ := hatom
  exact rowColorAtoms_outside_counterNamespace
    reservedA reservedQ reservedPhase targetA r atom hatom

theorem counterSpecs_wellFormed (kind : Kind) :
    ManyCounterWellFormed (ProfileDFourRowCNF.fmla kind) counterSpecs := by
  refine ⟨counterSpecs_tags_nodup, ?_, ?_⟩
  · intro reserved hreserved
    have hreserved' : reserved ∈ counterSpecs := hreserved
    simp only [counterSpecs, List.mem_map] at hreserved'
    obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hreserved'
    exact ProfileDThresholdCappedCNF.fmla_outside_counterNamespace
      kind (namespaceVertex a phase) q
  · intro reserved hreserved target htarget
    have hreserved' : reserved ∈ counterSpecs := hreserved
    have htarget' : target ∈ counterSpecs := htarget
    simp only [counterSpecs, List.mem_map] at hreserved' htarget'
    obtain ⟨⟨reservedA, reservedQ, reservedPhase⟩,
      _hreservedContext, rfl⟩ := hreserved'
    obtain ⟨⟨targetA, targetQ, targetPhase⟩,
      _htargetContext, rfl⟩ := htarget'
    unfold counterSpec
    change InputsOutsideNamespace
      (counterTag reservedA reservedQ reservedPhase)
      (contextInputs targetA targetQ targetPhase)
    unfold contextInputs
    split
    · exact rowColorAtoms_outside_counterNamespace
        reservedA reservedQ reservedPhase targetA targetQ
    · exact rowOtherColorAtoms_outside_counterNamespace
        reservedA reservedQ reservedPhase targetA targetQ

/-! ## Degree-floored semantic models -/

theorem allCaps_of_degreeFlooredFourExtension {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    AllCaps counterSpecs
      (coloringValuation (totalColoring ext.toFourExtension)) := by
  intro spec hspec
  have hspec' : spec ∈ counterSpecs := hspec
  simp only [counterSpecs, List.mem_map] at hspec'
  obtain ⟨⟨a, q, phase⟩, _hcontext, rfl⟩ := hspec'
  unfold InputsAtMost counterSpec
  change trueInputCount
      (coloringValuation (totalColoring ext.toFourExtension))
      (contextInputs a q phase) ≤ contextBound q phase
  by_cases hphase : phase = upperPhase
  · simp only [contextInputs, contextBound, hphase, ↓reduceIte]
    rw [trueInputCount_rowColorAtoms]
    by_cases hq : q = 0
    · subst q
      simpa [supportUpperBound] using ext.zeroSupportUpper a
    · simpa [supportUpperBound, hq] using
        ext.nonzeroSupportUpper a q hq
  · simp only [contextInputs, contextBound, hphase, ↓reduceIte]
    rw [trueInputCount_rowOtherColorAtoms]
    by_cases hq : q = 0
    · subst q
      have hlower := ext.zeroSupportLower a
      simp only [complementaryUpperBound, ↓reduceIte]
      omega
    · have hlower := ext.nonzeroSupportLower a q hq
      simp only [complementaryUpperBound, hq, ↓reduceIte]
      omega

/-- The exact degree-floored formula for one fixed profile-D kind. -/
def fmla (kind : Kind) : Sat.Fmla :=
  manySequentialAtMostFmla (ProfileDFourRowCNF.fmla kind) counterSpecs

theorem degreeFlooredFourExtension_satisfies_fmla {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    (iteratedSequentialExtension counterSpecs
      (coloringValuation
        (totalColoring ext.toFourExtension))).satisfies_fmla
      (fmla kind) := by
  exact iteratedExtension_satisfies_manySequentialAtMostFmla
    (ProfileDFourRowCNF.fmla kind) counterSpecs
    (coloringValuation (totalColoring ext.toFourExtension))
    (counterSpecs_wellFormed kind)
    (ProfileDFourRowCNF.fourExtension_satisfies_fmla ext.toFourExtension)
    (allCaps_of_degreeFlooredFourExtension ext)

theorem noDegreeFlooredFourExtension_of_lrat (kind : Kind)
    (hunsat : (fmla kind).proof []) :
    ¬Nonempty (DegreeFlooredFourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat _ (degreeFlooredFourExtension_satisfies_fmla ext)

/-! ## Six checked representatives and the profile-D endpoint -/

/-- The six representatives left by the equal-K15 block swap.  This
structure declares certificate slots but supplies no inhabitant. -/
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

theorem RepresentativeLRATRefutations.universalObstruction
    (h : RepresentativeLRATRefutations) :
    UniversalDegreeFlooredFourRowObstruction :=
  h.obstructions.universal

theorem no_profileD_star_of_degreeFloored_lrat
    (h : RepresentativeLRATRefutations) :
    ¬Nonempty
      (SingleRootStarCNF.CanonicalStarWitness ProfileD) :=
  no_profileD_star_of_swapRepresentativeDegreeFlooredObstructions
    h.obstructions

#print axioms R4333.ProfileDDegreeFlooredCNF.trueInputCount_rowColorAtoms
#print axioms R4333.ProfileDDegreeFlooredCNF.trueInputCount_rowOtherColorAtoms
#print axioms R4333.ProfileDDegreeFlooredCNF.counterSpecs_wellFormed
#print axioms R4333.ProfileDDegreeFlooredCNF.allCaps_of_degreeFlooredFourExtension
#print axioms R4333.ProfileDDegreeFlooredCNF.degreeFlooredFourExtension_satisfies_fmla
#print axioms R4333.ProfileDDegreeFlooredCNF.noDegreeFlooredFourExtension_of_lrat
#print axioms R4333.ProfileDDegreeFlooredCNF.RepresentativeLRATRefutations.obstructions
#print axioms R4333.ProfileDDegreeFlooredCNF.no_profileD_star_of_degreeFloored_lrat

end ProfileDDegreeFlooredCNF
end R4333
