import R4333Lean.OutsideDegreeCapCNF
import R4333Lean.SequentialAtMostManyCNF

/-!
# Reusable degree-cap counters for threshold colourings

The threshold row formulas all encode a colouring on `Fin 50` and omit one
distinguished Ramsey root.  A semantic extension therefore supplies two
families of degree bounds:

* the degree in each vertex's omitted-root colour is at most fifteen; and
* every displayed colour degree is at most sixteen.

This file turns those mathematical bounds into two exact ordered families of
sequential counters.  `ownDegreeCounterSpecs` contains one bound-fifteen
counter per vertex.  `allDegreeCounterSpecs` contains one counter per
vertex/colour pair, with bound fifteen in the omitted-root colour and sixteen
otherwise.  The vertex-major, colour-minor order and auxiliary namespaces are
part of the trusted Lean definition.

No unsatisfiability certificate is asserted here.
-/

namespace R4333

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF

namespace ThresholdDegreeCapsCNF

/-! ## Small formula-shape helpers -/

/-- Formula namespace avoidance is preserved by clause-list append. -/
theorem formulaOutsideNamespace_append {tag : Nat} {left right : Sat.Fmla}
    (hleft : FormulaOutsideNamespace tag left)
    (hright : FormulaOutsideNamespace tag right) :
    FormulaOutsideNamespace tag (left ++ right) := by
  intro clause hclause literal hliteral
  rcases List.mem_append.mp hclause with hclause | hclause
  · exact hleft clause hclause literal hliteral
  · exact hright clause hclause literal hliteral

/-- Any list of positive unit clauses on in-range edge atoms avoids every
degree-counter namespace for the same vertex set. -/
theorem positiveEdgeUnitClauses_outside_counterNamespace
    {α : Type*} {n k : Nat} (pairs : List α)
    (left right color : α → Nat)
    (reservedX : Fin n) (reservedQ : Fin k)
    (hleft : ∀ pair ∈ pairs, left pair < n)
    (hright : ∀ pair ∈ pairs, right pair < n) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (pairs.map fun pair =>
        [Sat.Literal.pos (edgeAtom (left pair) (right pair) (color pair))]) := by
  intro clause hclause literal hliteral
  obtain ⟨pair, hpair, hclauseEq⟩ := List.mem_map.mp hclause
  have hliteral' : literal ∈
      [Sat.Literal.pos (edgeAtom (left pair) (right pair) (color pair))] := by
    rw [hclauseEq]
    exact hliteral
  simp only [List.mem_singleton] at hliteral'
  subst literal
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    reservedX reservedQ (hleft pair hpair) (hright pair hpair)

/-- Negative edge-unit counterpart of
`positiveEdgeUnitClauses_outside_counterNamespace`. -/
theorem negativeEdgeUnitClauses_outside_counterNamespace
    {α : Type*} {n k : Nat} (pairs : List α)
    (left right color : α → Nat)
    (reservedX : Fin n) (reservedQ : Fin k)
    (hleft : ∀ pair ∈ pairs, left pair < n)
    (hright : ∀ pair ∈ pairs, right pair < n) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (pairs.map fun pair =>
        [Sat.Literal.neg (edgeAtom (left pair) (right pair) (color pair))]) := by
  intro clause hclause literal hliteral
  obtain ⟨pair, hpair, hclauseEq⟩ := List.mem_map.mp hclause
  have hliteral' : literal ∈
      [Sat.Literal.neg (edgeAtom (left pair) (right pair) (color pair))] := by
    rw [hclauseEq]
    exact hliteral
  simp only [List.mem_singleton] at hliteral'
  subst literal
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    reservedX reservedQ (hleft pair hpair) (hright pair hpair)

/-! ## Exact ordered counter families -/

/-- One bound-fifteen incident-edge counter for every vertex, in `Fin` order. -/
def ownDegreeCounterSpecs {n k : Nat}
    (rootColor : Fin n → Fin k) : List CounterSpec :=
  (List.finRange n).map fun x =>
    { tag := OutsideDegreeCapCNF.outsideDegreeCounterTag x (rootColor x)
      bound := 15
      inputs := OutsideDegreeCapCNF.outsideIncidentAtoms x (rootColor x) }

/-- Vertex-major, colour-minor enumeration used by the complete cap family. -/
def vertexColorPairs (n k : Nat) : List (Fin n × Fin k) :=
  (List.finRange n).product (List.finRange k)

/-- The exact threshold bound for one displayed vertex/colour pair. -/
def thresholdDegreeBound {n k : Nat}
    (rootColor : Fin n → Fin k) (x : Fin n) (q : Fin k) : Nat :=
  if q = rootColor x then 15 else 16

/-- One counter for every vertex/colour pair, in vertex-major order. -/
def allDegreeCounterSpecs {n k : Nat}
    (rootColor : Fin n → Fin k) : List CounterSpec :=
  (vertexColorPairs n k).map fun pair =>
    { tag := OutsideDegreeCapCNF.outsideDegreeCounterTag pair.1 pair.2
      bound := thresholdDegreeBound rootColor pair.1 pair.2
      inputs := OutsideDegreeCapCNF.outsideIncidentAtoms pair.1 pair.2 }

/-- Append exactly the `n` own-root-colour counters to an arbitrary base. -/
def withOwnDegreeCapsFmla {n k : Nat} (base : Sat.Fmla)
    (rootColor : Fin n → Fin k) : Sat.Fmla :=
  manySequentialAtMostFmla base (ownDegreeCounterSpecs rootColor)

/-- Append exactly the `n*k` threshold counters to an arbitrary base. -/
def withAllDegreeCapsFmla {n k : Nat} (base : Sat.Fmla)
    (rootColor : Fin n → Fin k) : Sat.Fmla :=
  manySequentialAtMostFmla base (allDegreeCounterSpecs rootColor)

theorem ownDegreeCounterSpecs_length {n k : Nat}
    (rootColor : Fin n → Fin k) :
    (ownDegreeCounterSpecs rootColor).length = n := by
  simp [ownDegreeCounterSpecs]

theorem vertexColorPairs_length (n k : Nat) :
    (vertexColorPairs n k).length = n * k := by
  calc
    (vertexColorPairs n k).length =
        (List.finRange n).length * (List.finRange k).length :=
      List.length_product _ _
    _ = n * k := by simp

theorem allDegreeCounterSpecs_length {n k : Nat}
    (rootColor : Fin n → Fin k) :
    (allDegreeCounterSpecs rootColor).length = n * k := by
  rw [allDegreeCounterSpecs, List.length_map, vertexColorPairs_length]

/-! ## Namespace contracts -/

theorem ownDegreeCounterSpecs_tags_nodup {n k : Nat}
    (rootColor : Fin n → Fin k) :
    ((ownDegreeCounterSpecs rootColor).map CounterSpec.tag).Nodup := by
  unfold ownDegreeCounterSpecs
  rw [List.map_map]
  apply (List.nodup_finRange n).map
  intro x y htag
  exact (OutsideDegreeCapCNF.outsideDegreeCounterTag_injective htag).1

theorem vertexColorPairs_nodup (n k : Nat) :
    (vertexColorPairs n k).Nodup := by
  exact (List.nodup_finRange n).product (List.nodup_finRange k)

theorem allDegreeCounterSpecs_tags_nodup {n k : Nat}
    (rootColor : Fin n → Fin k) :
    ((allDegreeCounterSpecs rootColor).map CounterSpec.tag).Nodup := by
  unfold allDegreeCounterSpecs
  rw [List.map_map]
  apply (vertexColorPairs_nodup n k).map
  intro left right htag
  obtain ⟨hx, hq⟩ :=
    OutsideDegreeCapCNF.outsideDegreeCounterTag_injective htag
  exact Prod.ext hx hq

/-- The only profile-specific namespace obligation for the `n`-counter
formula is that its base avoid each selected `(vertex, root colour)` tag. -/
theorem ownDegreeCounterSpecs_wellFormed {n k : Nat}
    (base : Sat.Fmla) (rootColor : Fin n → Fin k)
    (hbase : ∀ x : Fin n, FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag x (rootColor x)) base) :
    ManyCounterWellFormed base (ownDegreeCounterSpecs rootColor) := by
  refine ⟨ownDegreeCounterSpecs_tags_nodup rootColor, ?_, ?_⟩
  · intro reserved hreserved
    have hreserved' : reserved ∈ ownDegreeCounterSpecs rootColor := hreserved
    simp only [ownDegreeCounterSpecs, List.mem_map] at hreserved'
    obtain ⟨x, _hx, rfl⟩ := hreserved'
    exact hbase x
  · intro reserved hreserved target htarget
    have hreserved' : reserved ∈ ownDegreeCounterSpecs rootColor := hreserved
    have htarget' : target ∈ ownDegreeCounterSpecs rootColor := htarget
    simp only [ownDegreeCounterSpecs, List.mem_map] at hreserved' htarget'
    obtain ⟨reservedX, _hr, rfl⟩ := hreserved'
    obtain ⟨targetX, _ht, rfl⟩ := htarget'
    exact OutsideDegreeCapCNF.outsideIncidentAtoms_outside_counterNamespace_for
      reservedX (rootColor reservedX) targetX (rootColor targetX)

/-- For the complete `n*k` family the base must avoid every degree-counter
namespace.  All counter-input obligations are then automatic. -/
theorem allDegreeCounterSpecs_wellFormed {n k : Nat}
    (base : Sat.Fmla) (rootColor : Fin n → Fin k)
    (hbase : ∀ x : Fin n, ∀ q : Fin k, FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag x q) base) :
    ManyCounterWellFormed base (allDegreeCounterSpecs rootColor) := by
  refine ⟨allDegreeCounterSpecs_tags_nodup rootColor, ?_, ?_⟩
  · intro reserved hreserved
    have hreserved' : reserved ∈ allDegreeCounterSpecs rootColor := hreserved
    simp only [allDegreeCounterSpecs, List.mem_map] at hreserved'
    obtain ⟨⟨x, q⟩, _hp, rfl⟩ := hreserved'
    exact hbase x q
  · intro reserved hreserved target htarget
    have hreserved' : reserved ∈ allDegreeCounterSpecs rootColor := hreserved
    have htarget' : target ∈ allDegreeCounterSpecs rootColor := htarget
    simp only [allDegreeCounterSpecs, List.mem_map] at hreserved' htarget'
    obtain ⟨⟨reservedX, reservedQ⟩, _hr, rfl⟩ := hreserved'
    obtain ⟨⟨targetX, targetQ⟩, _ht, rfl⟩ := htarget'
    exact OutsideDegreeCapCNF.outsideIncidentAtoms_outside_counterNamespace_for
      reservedX reservedQ targetX targetQ

/-! ## Exact mathematical meaning -/

/-- Identity-palette specialization of the general incident-atom count. -/
theorem trueInputCount_incidentAtoms {n k : Nat}
    (d : EdgeColoring (Fin n) (Fin k)) (x : Fin n) (q : Fin k) :
    trueInputCount (coloringValuation d)
        (OutsideDegreeCapCNF.outsideIncidentAtoms x q) =
      colorDegree d q x := by
  have h := OutsideDegreeCapCNF.trueInputCount_outsideIncidentAtoms
    (Equiv.refl (Fin k)) d x q
  have hmap : OutsideCoreCNF.paletteMappedColoring
      (Equiv.refl (Fin k)) d = d := by
    apply EdgeColoring.ext
    rfl
  rw [hmap] at h
  exact h

/-- The semantic own-root degree bound supplies all `n` mathematical caps. -/
theorem allCaps_of_ownDegreeBounds {n k : Nat}
    (rootColor : Fin n → Fin k) (d : EdgeColoring (Fin n) (Fin k))
    (hdegree : ∀ x : Fin n, colorDegree d (rootColor x) x ≤ 15) :
    AllCaps (ownDegreeCounterSpecs rootColor) (coloringValuation d) := by
  intro spec hspec
  have hspec' : spec ∈ ownDegreeCounterSpecs rootColor := hspec
  simp only [ownDegreeCounterSpecs, List.mem_map] at hspec'
  obtain ⟨x, _hx, rfl⟩ := hspec'
  unfold InputsAtMost
  rw [trueInputCount_incidentAtoms d x (rootColor x)]
  exact hdegree x

/-- Own-root degree fifteen together with the universal degree-sixteen bound
supplies every cap in the complete `n*k` family. -/
theorem allCaps_of_thresholdDegreeBounds {n k : Nat}
    (rootColor : Fin n → Fin k) (d : EdgeColoring (Fin n) (Fin k))
    (hown : ∀ x : Fin n, colorDegree d (rootColor x) x ≤ 15)
    (hall : ∀ x : Fin n, ∀ q : Fin k, colorDegree d q x ≤ 16) :
    AllCaps (allDegreeCounterSpecs rootColor) (coloringValuation d) := by
  intro spec hspec
  have hspec' : spec ∈ allDegreeCounterSpecs rootColor := hspec
  simp only [allDegreeCounterSpecs, List.mem_map] at hspec'
  obtain ⟨⟨x, q⟩, _hp, rfl⟩ := hspec'
  unfold InputsAtMost
  rw [trueInputCount_incidentAtoms d x q]
  unfold thresholdDegreeBound
  by_cases hq : q = rootColor x
  · subst q
    simp [hown x]
  · simp [hq, hall x q]

/-! ## Checked-refutation boundaries -/

/-- A semantic colouring satisfying the base and every own-root degree cap
extends to a model of the exact `n`-counter formula. -/
theorem coloring_satisfies_withOwnDegreeCapsFmla {n k : Nat}
    (base : Sat.Fmla) (rootColor : Fin n → Fin k)
    (d : EdgeColoring (Fin n) (Fin k))
    (houtside : ∀ x : Fin n, FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag x (rootColor x)) base)
    (hbase : (coloringValuation d).satisfies_fmla base)
    (hdegree : ∀ x : Fin n, colorDegree d (rootColor x) x ≤ 15) :
    (iteratedSequentialExtension (ownDegreeCounterSpecs rootColor)
      (coloringValuation d)).satisfies_fmla
        (withOwnDegreeCapsFmla base rootColor) := by
  exact iteratedExtension_satisfies_manySequentialAtMostFmla
    base (ownDegreeCounterSpecs rootColor) (coloringValuation d)
    (ownDegreeCounterSpecs_wellFormed base rootColor houtside) hbase
    (allCaps_of_ownDegreeBounds rootColor d hdegree)

/-- Complete-family counterpart of `coloring_satisfies_withOwnDegreeCapsFmla`. -/
theorem coloring_satisfies_withAllDegreeCapsFmla {n k : Nat}
    (base : Sat.Fmla) (rootColor : Fin n → Fin k)
    (d : EdgeColoring (Fin n) (Fin k))
    (houtside : ∀ x : Fin n, ∀ q : Fin k, FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag x q) base)
    (hbase : (coloringValuation d).satisfies_fmla base)
    (hown : ∀ x : Fin n, colorDegree d (rootColor x) x ≤ 15)
    (hall : ∀ x : Fin n, ∀ q : Fin k, colorDegree d q x ≤ 16) :
    (iteratedSequentialExtension (allDegreeCounterSpecs rootColor)
      (coloringValuation d)).satisfies_fmla
        (withAllDegreeCapsFmla base rootColor) := by
  exact iteratedExtension_satisfies_manySequentialAtMostFmla
    base (allDegreeCounterSpecs rootColor) (coloringValuation d)
    (allDegreeCounterSpecs_wellFormed base rootColor houtside) hbase
    (allCaps_of_thresholdDegreeBounds rootColor d hown hall)

/-- Kernel-checked unsatisfiability of the own-cap formula rules out every
base colouring obeying the semantic bound-fifteen family. -/
theorem no_coloring_of_ownDegreeCaps_lrat {n k : Nat}
    (base : Sat.Fmla) (rootColor : Fin n → Fin k)
    (houtside : ∀ x : Fin n, FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag x (rootColor x)) base)
    (hunsat : (withOwnDegreeCapsFmla base rootColor).proof []) :
    ¬∃ d : EdgeColoring (Fin n) (Fin k),
      (coloringValuation d).satisfies_fmla base ∧
      ∀ x : Fin n, colorDegree d (rootColor x) x ≤ 15 := by
  rintro ⟨d, hbase, hdegree⟩
  exact hunsat _
    (coloring_satisfies_withOwnDegreeCapsFmla
      base rootColor d houtside hbase hdegree)

/-- Kernel-checked unsatisfiability of the complete cap formula rules out
every base colouring obeying both threshold degree families. -/
theorem no_coloring_of_allDegreeCaps_lrat {n k : Nat}
    (base : Sat.Fmla) (rootColor : Fin n → Fin k)
    (houtside : ∀ x : Fin n, ∀ q : Fin k, FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag x q) base)
    (hunsat : (withAllDegreeCapsFmla base rootColor).proof []) :
    ¬∃ d : EdgeColoring (Fin n) (Fin k),
      (coloringValuation d).satisfies_fmla base ∧
      (∀ x : Fin n, colorDegree d (rootColor x) x ≤ 15) ∧
      (∀ x : Fin n, ∀ q : Fin k, colorDegree d q x ≤ 16) := by
  rintro ⟨d, hbase, hown, hall⟩
  exact hunsat _
    (coloring_satisfies_withAllDegreeCapsFmla
      base rootColor d houtside hbase hown hall)

#print axioms R4333.ThresholdDegreeCapsCNF.ownDegreeCounterSpecs_wellFormed
#print axioms R4333.ThresholdDegreeCapsCNF.allDegreeCounterSpecs_wellFormed
#print axioms R4333.ThresholdDegreeCapsCNF.allCaps_of_thresholdDegreeBounds
#print axioms R4333.ThresholdDegreeCapsCNF.coloring_satisfies_withAllDegreeCapsFmla
#print axioms R4333.ThresholdDegreeCapsCNF.no_coloring_of_allDegreeCaps_lrat

end ThresholdDegreeCapsCNF
end R4333
