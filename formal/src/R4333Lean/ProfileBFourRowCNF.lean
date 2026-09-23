import R4333Lean.ProfileBCFourRowBoundary
import R4333Lean.FiniteColorCNF

/-!
# Exact checked-CNF boundary for the profile-B four-row obstruction

For each of the eight fixed tail-template kinds, the authoritative formula is
the ordinary Lean-generated four-colouring CNF on `Fin 51`, followed by:

1. 345 positive units fixing the internal `K15 + K16 + K16` tail templates,
   in block order, at vertex offsets `4 + 0`, `4 + 15`, and `4 + 31`; and
2. six negative units forbidding colour zero on the internal edges of the
   first four vertices.

The base has 92,225 clauses, so the full formula has 92,576 clauses.  The
vertex order is the four free vertices first and the 47 tail vertices second.
Atom identities are exactly `FiniteColorCNF.edgeAtom`; no external DIMACS map
is part of the trusted boundary.

This file proves that every semantic `FourExtension kind` satisfies the exact
formula and that a kernel-checked empty-clause proof refutes that semantic
object.  It supplies no unsatisfiability certificate.
-/

namespace R4333

open FiniteColorCNF
open SingleRootStarCNF

namespace ProfileBFourRowCNF

open ColoringJoinRows
open ProfileBRowExtension
open ProfileBFourRowBoundary

set_option maxRecDepth 1000000

abbrev TotalVertex := Fin 51

/-- The first four coordinates of the exact `Fin 51` vertex order. -/
def freeVertex (a : FourVertex) : TotalVertex :=
  ⟨a.val, by omega⟩

/-- The tail coordinates `4,...,50` of the exact `Fin 51` vertex order. -/
def tailVertex (x : TailVertex) : TotalVertex :=
  ⟨4 + x.val, by omega⟩

/-- Decode the exact `Fin 51` order into the semantic sum used by
`joinColoring`. -/
def splitVertex (v : TotalVertex) : Sum FourVertex TailVertex :=
  if h : v.val < 4 then
    .inl ⟨v.val, h⟩
  else
    .inr ⟨v.val - 4, by omega⟩

/-- Reassemble the semantic sum in the exact `Fin 51` order. -/
def mergeVertex : Sum FourVertex TailVertex → TotalVertex
  | .inl a => freeVertex a
  | .inr x => tailVertex x

theorem mergeVertex_splitVertex (v : TotalVertex) :
    mergeVertex (splitVertex v) = v := by
  by_cases h : v.val < 4
  · apply Fin.ext
    simp [mergeVertex, splitVertex, freeVertex, h]
  · apply Fin.ext
    simp [mergeVertex, splitVertex, tailVertex, h]
    omega

theorem splitVertex_injective : Function.Injective splitVertex := by
  intro x y hxy
  rw [← mergeVertex_splitVertex x, hxy, mergeVertex_splitVertex y]

@[simp] theorem splitVertex_freeVertex (a : FourVertex) :
    splitVertex (freeVertex a) = .inl a := by
  simp [splitVertex, freeVertex, a.isLt]

@[simp] theorem splitVertex_tailVertex (x : TailVertex) :
    splitVertex (tailVertex x) = .inr x := by
  have hnot : ¬4 + x.val < 4 := by omega
  simp [splitVertex, tailVertex, hnot]

/-- The semantic four-row object reindexed as one colouring on `Fin 51`. -/
def totalColoring {kind : Kind} (ext : FourExtension kind) :
    EdgeColoring TotalVertex (Fin 4) :=
  pullbackColoring
    (joinColoring ext.inside ext.tail.coloring ext.rows) splitVertex

@[simp] theorem totalColoring_free_free {kind : Kind}
    (ext : FourExtension kind) (a b : FourVertex) :
    totalColoring ext (freeVertex a) (freeVertex b) = ext.inside a b := by
  simp [totalColoring, pullbackColoring]

@[simp] theorem totalColoring_tail_tail {kind : Kind}
    (ext : FourExtension kind) (x y : TailVertex) :
    totalColoring ext (tailVertex x) (tailVertex y) = ext.tail.coloring x y := by
  simp [totalColoring, pullbackColoring]

theorem totalColoring_noMono {kind : Kind} (ext : FourExtension kind) :
    NoMonochromaticTriangle (totalColoring ext) := by
  apply noMono_pullback
    (joinColoring ext.inside ext.tail.coloring ext.rows)
    splitVertex splitVertex_injective
  exact (noMono_joinColoring_iff
    ext.inside ext.tail.coloring ext.rows).2
      ⟨ext.insideNoMono, ext.tail.noMono,
        ext.rowsAdmissible, ext.rowsPairCompatible⟩

/-- Positive units for one shifted internal tail block. -/
def blockTemplateUnitClauses (kind : Kind) (block : Fin 3) : Sat.Fmla :=
  (FiniteColorCNF.edges (blockSize block)).map fun pair =>
    [Sat.Literal.pos (FiniteColorCNF.edgeAtom
      (4 + blockStart block + pair.1)
      (4 + blockStart block + pair.2)
      (canonicalPalette (Fin.succ block)
        (templateColor (blockSize block) (kind.twisted block)
          pair.1 pair.2)).val)]

/-- Exact positive-unit order: K15, first K16, then second K16. -/
def templateUnitClauses (kind : Kind) : Sat.Fmla :=
  blockTemplateUnitClauses kind 0 ++
    blockTemplateUnitClauses kind 1 ++
      blockTemplateUnitClauses kind 2

/-- Six lexicographically ordered negative units for colour zero on K4. -/
def insideRootForbiddenUnitClauses : Sat.Fmla :=
  (FiniteColorCNF.edges 4).map fun pair =>
    [Sat.Literal.neg (FiniteColorCNF.edgeAtom pair.1 pair.2 0)]

/-- Authoritative full formula.  Clause order is base, 345 template units,
then six root-forbidden units. -/
def fmla (kind : Kind) : Sat.Fmla :=
  FiniteColorCNF.goodColoringFmla 51 4 ++
    templateUnitClauses kind ++ insideRootForbiddenUnitClauses

theorem goodColoringFmla_length :
    (FiniteColorCNF.goodColoringFmla 51 4).length = 92225 := by decide

theorem templateUnitClauses_length (kind : Kind) :
    (templateUnitClauses kind).length = 345 := by
  cases kind <;> decide

theorem insideRootForbiddenUnitClauses_length :
    insideRootForbiddenUnitClauses.length = 6 := by decide

theorem fmla_length (kind : Kind) : (fmla kind).length = 92576 := by
  simp [fmla, goodColoringFmla_length, templateUnitClauses_length,
    insideRootForbiddenUnitClauses_length]

private theorem fourExtension_satisfies_blockTemplateUnitClauses
    {kind : Kind} (ext : FourExtension kind) (block : Fin 3) :
    (FiniteColorCNF.coloringValuation (totalColoring ext)).satisfies_fmla
      (blockTemplateUnitClauses kind block) := by
  constructor
  intro clause hclause
  simp only [blockTemplateUnitClauses, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  obtain ⟨hleft, hright, hlr⟩ :=
    SingleRootStarCNF.mem_edges_bounds hpair
  let leftTail : TailVertex := blockVertex block pair.1
  let rightTail : TailVertex := blockVertex block pair.2
  let left : TotalVertex := tailVertex leftTail
  let right : TotalVertex := tailVertex rightTail
  let q : Fin 4 := canonicalPalette (Fin.succ block)
    (templateColor (blockSize block) (kind.twisted block) pair.1 pair.2)
  have hleftVal : left.val = 4 + blockStart block + pair.1 := by
    simp [left, leftTail, tailVertex, blockVertex_val block hleft]
    omega
  have hrightVal : right.val = 4 + blockStart block + pair.2 := by
    simp [right, rightTail, tailVertex, blockVertex_val block hright]
    omega
  have hcritical : isCriticalBlock ProfileB (Fin.succ block) := by
    fin_cases block <;> decide
  apply FiniteColorCNF.satisfies_of_mem_holds
    (FiniteColorCNF.coloringValuation (totalColoring ext))
    (l := Sat.Literal.pos (FiniteColorCNF.edgeAtom
      (4 + blockStart block + pair.1)
      (4 + blockStart block + pair.2) q.val))
  · exact List.Mem.head _
  · change FiniteColorCNF.coloringValuation (totalColoring ext)
      (FiniteColorCNF.edgeAtom
        (4 + blockStart block + pair.1)
        (4 + blockStart block + pair.2) q.val)
    rw [← hleftVal, ← hrightVal]
    rw [FiniteColorCNF.coloringValuation_edgeAtom]
    change totalColoring ext (tailVertex leftTail) (tailVertex rightTail) = q
    rw [totalColoring_tail_tail]
    exact ext.tail.templateCanonical block hcritical pair.1 pair.2
      hleft hright hlr

theorem fourExtension_satisfies_templateUnitClauses
    {kind : Kind} (ext : FourExtension kind) :
    (FiniteColorCNF.coloringValuation (totalColoring ext)).satisfies_fmla
      (templateUnitClauses kind) := by
  constructor
  intro clause hclause
  simp only [templateUnitClauses, List.mem_append] at hclause
  rcases hclause with (hzero | hone) | htwo
  · exact (fourExtension_satisfies_blockTemplateUnitClauses ext 0).prop
      clause hzero
  · exact (fourExtension_satisfies_blockTemplateUnitClauses ext 1).prop
      clause hone
  · exact (fourExtension_satisfies_blockTemplateUnitClauses ext 2).prop
      clause htwo

theorem fourExtension_satisfies_insideRootForbiddenUnitClauses
    {kind : Kind} (ext : FourExtension kind) :
    (FiniteColorCNF.coloringValuation (totalColoring ext)).satisfies_fmla
      insideRootForbiddenUnitClauses := by
  constructor
  intro clause hclause
  simp only [insideRootForbiddenUnitClauses, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  obtain ⟨hleft, hright, hlr⟩ :=
    SingleRootStarCNF.mem_edges_bounds hpair
  let leftFree : FourVertex := ⟨pair.1, hleft⟩
  let rightFree : FourVertex := ⟨pair.2, hright⟩
  let left : TotalVertex := freeVertex leftFree
  let right : TotalVertex := freeVertex rightFree
  let zero : Fin 4 := 0
  have hleftVal : left.val = pair.1 := rfl
  have hrightVal : right.val = pair.2 := rfl
  apply FiniteColorCNF.satisfies_of_mem_holds
    (FiniteColorCNF.coloringValuation (totalColoring ext))
    (l := Sat.Literal.neg (FiniteColorCNF.edgeAtom pair.1 pair.2 0))
  · exact List.Mem.head _
  · change ¬FiniteColorCNF.coloringValuation (totalColoring ext)
      (FiniteColorCNF.edgeAtom pair.1 pair.2 zero.val)
    rw [← hleftVal, ← hrightVal]
    rw [FiniteColorCNF.coloringValuation_edgeAtom]
    change totalColoring ext (freeVertex leftFree) (freeVertex rightFree) ≠ zero
    rw [totalColoring_free_free]
    exact ext.insideRootForbidden leftFree rightFree (Fin.ne_of_lt hlr)

/-- Every exact semantic object satisfies the exact Lean-generated formula. -/
theorem fourExtension_satisfies_fmla {kind : Kind}
    (ext : FourExtension kind) :
    (FiniteColorCNF.coloringValuation (totalColoring ext)).satisfies_fmla
      (fmla kind) := by
  constructor
  intro clause hclause
  simp only [fmla, List.mem_append] at hclause
  rcases hclause with (hbase | htemplate) | hforbidden
  · exact (FiniteColorCNF.coloring_satisfies_goodColoringFmla
      (totalColoring ext) (totalColoring_noMono ext)).prop clause hbase
  · exact (fourExtension_satisfies_templateUnitClauses ext).prop
      clause htemplate
  · exact (fourExtension_satisfies_insideRootForbiddenUnitClauses ext).prop
      clause hforbidden

/-- A checked empty-clause proof for one fixed kind refutes its exact
four-row semantic object. -/
theorem noFourExtension_of_lrat (kind : Kind)
    (hunsat : (fmla kind).proof Sat.Clause.nil) :
    ¬Nonempty (FourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat (FiniteColorCNF.coloringValuation (totalColoring ext))
    (fourExtension_satisfies_fmla ext)

/-- The eight exact certificate endpoints.  This structure contains no
asserted certificates. -/
structure LRATRefutations : Prop where
  uuu : (fmla .uuu).proof Sat.Clause.nil
  uut : (fmla .uut).proof Sat.Clause.nil
  utu : (fmla .utu).proof Sat.Clause.nil
  utt : (fmla .utt).proof Sat.Clause.nil
  tuu : (fmla .tuu).proof Sat.Clause.nil
  tut : (fmla .tut).proof Sat.Clause.nil
  ttu : (fmla .ttu).proof Sat.Clause.nil
  ttt : (fmla .ttt).proof Sat.Clause.nil

theorem LRATRefutations.proof (h : LRATRefutations) (kind : Kind) :
    (fmla kind).proof Sat.Clause.nil := by
  cases kind with
  | uuu => exact h.uuu
  | uut => exact h.uut
  | utu => exact h.utu
  | utt => exact h.utt
  | tuu => exact h.tuu
  | tut => exact h.tut
  | ttu => exact h.ttu
  | ttt => exact h.ttt

theorem LRATRefutations.universalFourRowObstruction
    (h : LRATRefutations) : UniversalFourRowObstruction := fun kind =>
  noFourExtension_of_lrat kind (h.proof kind)

/-- Eight checked four-row refutations eliminate the full profile-B branch. -/
theorem no_profileB_star_of_lrat (h : LRATRefutations) :
    ¬Nonempty (CanonicalStarWitness ProfileB) :=
  no_profileB_star_of_universalFourRowObstruction
    h.universalFourRowObstruction

#print axioms R4333.ProfileBFourRowCNF.totalColoring_noMono
#print axioms R4333.ProfileBFourRowCNF.fourExtension_satisfies_fmla
#print axioms R4333.ProfileBFourRowCNF.noFourExtension_of_lrat
#print axioms R4333.ProfileBFourRowCNF.LRATRefutations.universalFourRowObstruction
#print axioms R4333.ProfileBFourRowCNF.no_profileB_star_of_lrat

end ProfileBFourRowCNF

end R4333
