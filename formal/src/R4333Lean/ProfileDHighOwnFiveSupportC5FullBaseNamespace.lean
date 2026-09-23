import R4333Lean.ProfileDHighOwnFiveSupportC5BaseNamespace

namespace R4333
namespace ProfileDHighOwnFiveSupportC5FullBaseNamespace

open FiniteColorCNF SequentialAtMostCNF ThresholdDegreeCapsCNF
open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5LRAT
open ProfileDHighOwnFiveSupportC5BaseNamespace

abbrev Kind := ProfileDTripleJoinReduction.Kind

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The pilot-compatible tags live in a synthetic `Fin 52` namespace, while
the semantic base is `K_51`.  This is the slightly more general namespace
fact obtained by replaying the ordinary good-colouring clause cases and
using `51 < 52` for every endpoint. -/
private theorem goodColoringFmla51_outside_counterNamespace
    (reserved : CounterContext) :
    FormulaOutsideNamespace (counterTag reserved)
      (FiniteColorCNF.goodColoringFmla 51 4) := by
  intro clause hclause literal hliteral
  have hclause' : clause ∈ FiniteColorCNF.goodColoringFmla 51 4 := hclause
  simp only [FiniteColorCNF.goodColoringFmla, List.mem_append] at hclause'
  rcases hclause' with (hatLeast | hatMost) | htriangle
  · simp only [FiniteColorCNF.atLeastOneClauses, List.mem_map] at hatLeast
    obtain ⟨⟨a, b⟩, hedge, rfl⟩ := hatLeast
    change List.Mem literal
      ((List.range 4).map fun q => Sat.Literal.pos (edgeAtom a b q))
      at hliteral
    have hliteral' : literal ∈
        ((List.range 4).map fun q => Sat.Literal.pos (edgeAtom a b q)) :=
      hliteral
    simp only [List.mem_map] at hliteral'
    obtain ⟨q, _hq, rfl⟩ := hliteral'
    obtain ⟨ha, hb, _hab⟩ := SingleRootStarCNF.mem_edges_bounds hedge
    exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
      (namespaceVertex reserved) (namespaceColor reserved)
      (ha.trans (by omega)) (hb.trans (by omega))
  · simp only [FiniteColorCNF.atMostOneClauses, List.mem_flatMap,
      List.mem_map] at hatMost
    obtain ⟨⟨a, b⟩, hedge, ⟨⟨q, r⟩, _hqr, rfl⟩⟩ := hatMost
    change List.Mem literal
      [Sat.Literal.neg (edgeAtom a b q),
        Sat.Literal.neg (edgeAtom a b r)] at hliteral
    have hliteral' : literal ∈
        [Sat.Literal.neg (edgeAtom a b q),
          Sat.Literal.neg (edgeAtom a b r)] := hliteral
    simp at hliteral'
    obtain ⟨ha, hb, _hab⟩ := SingleRootStarCNF.mem_edges_bounds hedge
    rcases hliteral' with rfl | rfl <;>
      exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        (namespaceVertex reserved) (namespaceColor reserved)
        (ha.trans (by omega)) (hb.trans (by omega))
  · simp only [FiniteColorCNF.triangleClauses, List.mem_flatMap,
      List.mem_map] at htriangle
    obtain ⟨⟨a, b, d⟩, htriple, ⟨q, _hq, rfl⟩⟩ := htriangle
    obtain ⟨ha, hb, hd, _hab, _hbd⟩ :=
      FiniteColorCNF.mem_triples_iff_bounds htriple
    change List.Mem literal
      [Sat.Literal.neg (edgeAtom a b q),
        Sat.Literal.neg (edgeAtom a d q),
        Sat.Literal.neg (edgeAtom b d q)] at hliteral
    have hliteral' : literal ∈
        [Sat.Literal.neg (edgeAtom a b q),
          Sat.Literal.neg (edgeAtom a d q),
          Sat.Literal.neg (edgeAtom b d q)] := hliteral
    simp at hliteral'
    rcases hliteral' with rfl | rfl | rfl
    · exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        (namespaceVertex reserved) (namespaceColor reserved)
        (ha.trans (by omega)) (hb.trans (by omega))
    · exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        (namespaceVertex reserved) (namespaceColor reserved)
        (ha.trans (by omega)) (hd.trans (by omega))
    · exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        (namespaceVertex reserved) (namespaceColor reserved)
        (hb.trans (by omega)) (hd.trans (by omega))

/-- Every atom in the exact non-counter prefix avoids every one of the 42
reserved counter namespaces.  The fully explicit append tree prevents the
elaborator from normalizing the large `K51` clause list while solving
implicit list-split metavariables. -/
theorem baseFmla_outside_counterNamespace
    (kind : Kind) (block : Fin 3) (position : Fin (blockSize block))
    (reserved : CounterContext) :
    FormulaOutsideNamespace (counterTag reserved)
      (baseFmla kind block position) := by
  change FormulaOutsideNamespace (counterTag reserved)
    ((((FiniteColorCNF.goodColoringFmla 51 4 ++
      templateUnitClauses kind) ++
        insideRootForbiddenUnitClauses) ++
          allFiveOwnUnitClauses block position) ++
            insideC5UnitClauses block)
  exact formulaOutsideNamespace_append
    (formulaOutsideNamespace_append
      (formulaOutsideNamespace_append
        (formulaOutsideNamespace_append
          (goodColoringFmla51_outside_counterNamespace reserved)
          (templateUnitClauses_outside kind reserved))
        (insideRootForbiddenUnitClauses_outside reserved))
      (allFiveOwnUnitClauses_outside block position reserved))
    (insideC5UnitClauses_outside block reserved)

end ProfileDHighOwnFiveSupportC5FullBaseNamespace
end R4333
