import R4333Lean.Attaching61

/-!
# Exact labeled degree targets at order 61

The finite attaching encoders use 35 selectors: the distinct labeled
permutations of the five sorted degree patterns.  This file defines that
exact list in Lean and proves that every vertex of a hypothetical good K61
colouring selects one of its entries.
-/

namespace R4333

abbrev FourDegreeTuple := Nat × Nat × Nat × Nat

/-- The exact 35 labeled permutations of the five possible sorted degree
patterns.  Coordinates are `(00,01,10,11)`. -/
def degreeTargets61 : List FourDegreeTuple := [
  (12, 16, 16, 16),
  (13, 15, 16, 16),
  (13, 16, 15, 16),
  (13, 16, 16, 15),
  (14, 14, 16, 16),
  (14, 15, 15, 16),
  (14, 15, 16, 15),
  (14, 16, 14, 16),
  (14, 16, 15, 15),
  (14, 16, 16, 14),
  (15, 13, 16, 16),
  (15, 14, 15, 16),
  (15, 14, 16, 15),
  (15, 15, 14, 16),
  (15, 15, 15, 15),
  (15, 15, 16, 14),
  (15, 16, 13, 16),
  (15, 16, 14, 15),
  (15, 16, 15, 14),
  (15, 16, 16, 13),
  (16, 12, 16, 16),
  (16, 13, 15, 16),
  (16, 13, 16, 15),
  (16, 14, 14, 16),
  (16, 14, 15, 15),
  (16, 14, 16, 14),
  (16, 15, 13, 16),
  (16, 15, 14, 15),
  (16, 15, 15, 14),
  (16, 15, 16, 13),
  (16, 16, 12, 16),
  (16, 16, 13, 15),
  (16, 16, 14, 14),
  (16, 16, 15, 13),
  (16, 16, 16, 12)
]

theorem degreeTargets61_length : degreeTargets61.length = 35 := by decide

private def degreeValues61 : List Nat := [12, 13, 14, 15, 16]

/-- A small product-and-filter presentation of the same 35 tuples.  It is
convenient for the proof because membership can be introduced one coordinate
at a time, without asking arithmetic automation to discover a 35-way
disjunction. -/
private def generatedDegreeTargets61 : List FourDegreeTuple :=
  degreeValues61.flatMap fun a =>
    degreeValues61.flatMap fun b =>
      degreeValues61.flatMap fun c =>
        degreeValues61.flatMap fun d =>
          if a + b + c + d = 60 then [(a, b, c, d)] else []

private theorem generatedDegreeTargets61_eq :
    generatedDegreeTargets61 = degreeTargets61 := by decide

/-- Four nonnegative integers bounded by 16 and summing to 60 form exactly
one of the 35 labeled targets. -/
theorem degreeTuple_mem_degreeTargets61
    (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) :
    (a, b, c, d) ∈ degreeTargets61 := by
  have haMem : a ∈ degreeValues61 := by
    simp [degreeValues61]
    omega
  have hbMem : b ∈ degreeValues61 := by
    simp [degreeValues61]
    omega
  have hcMem : c ∈ degreeValues61 := by
    simp [degreeValues61]
    omega
  have hdMem : d ∈ degreeValues61 := by
    simp [degreeValues61]
    omega
  rw [← generatedDegreeTargets61_eq]
  refine List.mem_flatMap.mpr ⟨a, haMem, ?_⟩
  refine List.mem_flatMap.mpr ⟨b, hbMem, ?_⟩
  refine List.mem_flatMap.mpr ⟨c, hcMem, ?_⟩
  refine List.mem_flatMap.mpr ⟨d, hdMem, ?_⟩
  simp [hsum]

/-- The degree tuple of a vertex, in the fixed Boolean-pair colour order. -/
def fourColorDegreeTuple {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (v : V) : FourDegreeTuple :=
  (colorDegree c (false, false) v,
    colorDegree c (false, true) v,
    colorDegree c (true, false) v,
    colorDegree c (true, true) v)

/-- Every vertex of a good K61 four-colouring has one of the exact 35
labeled degree targets used by the finite encoder. -/
theorem fourColorDegreeTuple_mem_degreeTargets61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (v : V) :
    fourColorDegreeTuple c v ∈ degreeTargets61 := by
  apply degreeTuple_mem_degreeTargets61
  · exact fourColor_colorDegree_le_sixteen c hc (false, false) v
  · exact fourColor_colorDegree_le_sixteen c hc (false, true) v
  · exact fourColor_colorDegree_le_sixteen c hc (true, false) v
  · exact fourColor_colorDegree_le_sixteen c hc (true, true) v
  · have hsum := fourColor_degree_sum c v
    rw [hcard] at hsum
    simpa using hsum

#print axioms R4333.degreeTuple_mem_degreeTargets61
#print axioms R4333.fourColorDegreeTuple_mem_degreeTargets61

end R4333
