import R4333Lean.FiniteColorCNF
import R4333Lean.OutsideListBenders
import R4333Lean.ColorRelabel

/-!
# A Lean-defined CNF for outside restriction cores

An inner outside-list solver receives finitely many assumptions of the form
"edge `x-y` may not use colour `q`".  This file makes the exact formula
authoritative in Lean: the ordinary complete-graph colouring CNF is followed
by one negative unit clause for every restriction in an explicit list.

The semantic theorem is one-way in exactly the direction needed for a
certificate.  Every triangle-free outside colouring avoiding the listed
restrictions satisfies the generated formula.  Consequently a
kernel-checked LRAT refutation proves semantic core uncolourability and may
be fed directly to the Benders theorem.
-/

namespace R4333

open FiniteColorCNF

namespace OutsideCoreCNF

/-- An explicit computable enumeration of the four Boolean-pair colours.
It is the palette map used by the concrete order-61 outside formulas. -/
def fourColorEquivFin4 : FourColor ≃ Fin 4 :=
  (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans
    finProdFinEquiv

@[simp] theorem fourColorEquivFin4_false_false :
    fourColorEquivFin4 (false, false) = 0 := by decide

@[simp] theorem fourColorEquivFin4_false_true :
    fourColorEquivFin4 (false, true) = 1 := by decide

@[simp] theorem fourColorEquivFin4_true_false :
    fourColorEquivFin4 (true, false) = 2 := by decide

@[simp] theorem fourColorEquivFin4_true_true :
    fourColorEquivFin4 (true, true) = 3 := by decide

/-- The SAT atom used by one outside pair/colour restriction after mapping
the mathematical palette to `Fin k`. -/
def restrictionAtom {n k : ℕ} {C : Type*}
    (palette : C ≃ Fin k)
    (restriction : OutsidePairColorRestriction (Fin n) C) : ℕ :=
  edgeAtom restriction.left.val restriction.right.val
    (palette restriction.color).val

/-- One negative unit clause for each restriction, in the authoritative
list order.  Keeping a list (rather than choosing an order from a `Finset`)
makes external mirroring and LRAT reproduction exact. -/
def restrictionClauses {n k : ℕ} {C : Type*}
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C)) :
    Sat.Fmla :=
  restrictions.map fun restriction =>
    [Sat.Literal.neg (restrictionAtom palette restriction)]

/-- The exact inner formula: triangle-free complete-graph colouring plus
all list restrictions as negative units. -/
def outsideCoreFmla {C : Type*} (n k : ℕ)
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C)) :
    Sat.Fmla :=
  goodColoringFmla n k ++ restrictionClauses palette restrictions

@[simp] theorem restrictionClauses_length
    {n k : ℕ} {C : Type*} (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C)) :
    (restrictionClauses palette restrictions).length = restrictions.length := by
  simp [restrictionClauses]

theorem outsideCoreFmla_length
    {n k : ℕ} {C : Type*} (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C)) :
    (outsideCoreFmla n k palette restrictions).length =
      (goodColoringFmla n k).length + restrictions.length := by
  simp [outsideCoreFmla]

set_option maxRecDepth 1000000 in
/-- The exact clause count of the fixed unrestricted `K41` inner. -/
theorem goodColoringFmla_41_4_length :
    (goodColoringFmla 41 4).length = 48380 := by
  decide

/-- Pull a mathematical outside colouring through the finite palette used
by the canonical CNF. -/
def paletteMappedColoring {n k : ℕ} {C : Type*}
    (palette : C ≃ Fin k) (d : EdgeColoring (Fin n) C) :
    EdgeColoring (Fin n) (Fin k) :=
  mapEdgeColors d palette

theorem noMono_paletteMappedColoring {n k : ℕ} {C : Type*}
    (palette : C ≃ Fin k) (d : EdgeColoring (Fin n) C)
    (hd : NoMonochromaticTriangle d) :
    NoMonochromaticTriangle (paletteMappedColoring palette d) :=
  noMono_mapEdgeColors d palette hd

/-- A mathematical outside colouring avoiding every listed restriction
satisfies all generated negative unit clauses. -/
theorem coloring_satisfies_restrictionClauses
    {n k : ℕ} {C : Type*} [DecidableEq C]
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (d : EdgeColoring (Fin n) C)
    (havoids : OutsideColoringAvoidsCore d restrictions.toFinset) :
    (coloringValuation (paletteMappedColoring palette d)).satisfies_fmla
      (restrictionClauses palette restrictions) := by
  constructor
  intro clause hclause
  simp only [restrictionClauses, List.mem_map] at hclause
  obtain ⟨restriction, hmem, rfl⟩ := hclause
  apply satisfies_of_mem_holds
    (coloringValuation (paletteMappedColoring palette d))
    (l := Sat.Literal.neg (restrictionAtom palette restriction))
    (List.Mem.head _)
  change ¬coloringValuation (paletteMappedColoring palette d)
    (edgeAtom restriction.left restriction.right
      (palette restriction.color))
  rw [coloringValuation_edgeAtom]
  intro heq
  apply havoids restriction (List.mem_toFinset.mpr hmem)
  exact palette.injective heq

/-- Every mathematical outside colouring avoiding the restrictions
satisfies the full Lean-generated inner formula. -/
theorem coloring_satisfies_outsideCoreFmla
    {n k : ℕ} {C : Type*} [DecidableEq C]
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (d : EdgeColoring (Fin n) C)
    (hd : NoMonochromaticTriangle d)
    (havoids : OutsideColoringAvoidsCore d restrictions.toFinset) :
    (coloringValuation (paletteMappedColoring palette d)).satisfies_fmla
      (outsideCoreFmla n k palette restrictions) := by
  constructor
  intro clause hclause
  simp only [outsideCoreFmla, List.mem_append] at hclause
  rcases hclause with hbase | hrestrictions
  · exact (coloring_satisfies_goodColoringFmla
      (paletteMappedColoring palette d)
      (noMono_paletteMappedColoring palette d hd)).prop clause hbase
  · exact (coloring_satisfies_restrictionClauses
      palette restrictions d havoids).prop clause hrestrictions

/-- A checked LRAT refutation of the exact Lean formula proves the semantic
uncolourability required by `OutsideListBenders`. -/
theorem coreUnsatisfiable_of_lrat
    {n k : ℕ} {C : Type*} [DecidableEq C]
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (hunsat : (outsideCoreFmla n k palette restrictions).proof []) :
    OutsideRestrictionCoreUnsatisfiable restrictions.toFinset := by
  rintro ⟨d, hd, havoids⟩
  exact hunsat (coloringValuation (paletteMappedColoring palette d))
    (coloring_satisfies_outsideCoreFmla
      palette restrictions d hd havoids)

/-- End-to-end checked cut: an LRAT refutation of a Lean-defined inner core
forces the corresponding availability disjunction in any global completion.
The host and its exposed/outside embeddings remain completely generic. -/
theorem outsideListBendersClause_of_lrat
    {V E : Type*} {n k : ℕ} {C : Type*}
    [Fintype E] [DecidableEq C]
    (palette : C ≃ Fin k)
    (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : Fin n ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (hunsat : (outsideCoreFmla n k palette restrictions).proof []) :
    OutsideListBendersClause
      (coloringExposedIncidence c exposed outside)
      restrictions.toFinset := by
  exact outsideListBendersClause_of_coreUnsatisfiable c exposed outside
    hdisjoint hc restrictions.toFinset
    (coreUnsatisfiable_of_lrat palette restrictions hunsat)

#print axioms R4333.OutsideCoreCNF.coloring_satisfies_restrictionClauses
#print axioms R4333.OutsideCoreCNF.goodColoringFmla_41_4_length
#print axioms R4333.OutsideCoreCNF.coloring_satisfies_outsideCoreFmla
#print axioms R4333.OutsideCoreCNF.coreUnsatisfiable_of_lrat
#print axioms R4333.OutsideCoreCNF.outsideListBendersClause_of_lrat

end OutsideCoreCNF

end R4333
