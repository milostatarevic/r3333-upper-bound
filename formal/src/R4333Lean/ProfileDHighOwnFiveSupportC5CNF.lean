import R4333Lean.ProfileDHighOwnFiveRowSplit61
import R4333Lean.ThresholdDegreeCapsCNF

/-!
# Trusted CNF boundary for the profile-D five-support C5 branch

This module is deliberately separate from the semantic five-row split.  For
each profile-D tail kind, selected block, and selected position it defines an
exact `Fin 51` formula containing:

* the ordinary four-colour triangle-free base;
* all 330 canonical tail-template units;
* root-colour forbiddenness on the retained `K5`;
* the five selected own-colour column units;
* the block-adapted canonical `C5`/complement on the retained `K5`;
* all five native row-support intervals; and
* the sharp selected tail own-degree interval `[9,10]`.

The last interval is encoded directly on the 45 tail-tail edges incident to
the selected endpoint: at most ten own-colour atoms, and at most 36 atoms in
the other three colours, equivalently at least nine own-colour atoms.

All atoms, clause order, counter input order, and auxiliary namespaces are
Lean definitions.  The LRAT structures below are empty interfaces for future
checked certificates; this module supplies no certificate and makes no
unsatisfiability claim.
-/

namespace R4333
namespace ProfileDHighOwnFiveSupportC5CNF

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ThresholdDegreeCapsCNF ColoringJoinRows
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDRowSupportBounds61 ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FiveExtension := ProfileDHighOwnFiveRowSplit61.FiveExtension
abbrev DegreeFlooredFiveExtension :=
  ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension
abbrev FiveSupportFiveRowExtension :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension

/-! ## Exact `Fin 51` vertex order -/

abbrev TotalVertex := Fin 51

def freeVertex (a : FiveVertex) : TotalVertex :=
  ⟨a.val, by omega⟩

def tailVertex (x : TailVertex) : TotalVertex :=
  ⟨5 + x.val, by omega⟩

def splitVertex (v : TotalVertex) : Sum FiveVertex TailVertex :=
  if h : v.val < 5 then
    .inl ⟨v.val, h⟩
  else
    .inr ⟨v.val - 5, by omega⟩

def mergeVertex : Sum FiveVertex TailVertex → TotalVertex
  | .inl a => freeVertex a
  | .inr x => tailVertex x

theorem mergeVertex_splitVertex (v : TotalVertex) :
    mergeVertex (splitVertex v) = v := by
  by_cases h : v.val < 5
  · apply Fin.ext
    simp [mergeVertex, splitVertex, freeVertex, h]
  · apply Fin.ext
    simp [mergeVertex, splitVertex, tailVertex, h]
    omega

theorem splitVertex_injective : Function.Injective splitVertex := by
  intro x y hxy
  rw [← mergeVertex_splitVertex x, hxy, mergeVertex_splitVertex y]

@[simp] theorem splitVertex_freeVertex (a : FiveVertex) :
    splitVertex (freeVertex a) = .inl a := by
  simp [splitVertex, freeVertex, a.isLt]

@[simp] theorem splitVertex_tailVertex (x : TailVertex) :
    splitVertex (tailVertex x) = .inr x := by
  have hnot : ¬5 + x.val < 5 := by omega
  simp [splitVertex, tailVertex, hnot]

def totalColoring {kind : Kind} (ext : FiveExtension kind) :
    EdgeColoring TotalVertex (Fin 4) :=
  pullbackColoring
    (joinColoring ext.inside ext.tail.coloring ext.rows) splitVertex

@[simp] theorem totalColoring_free_free {kind : Kind}
    (ext : FiveExtension kind) (a b : FiveVertex) :
    totalColoring ext (freeVertex a) (freeVertex b) = ext.inside a b := by
  simp [totalColoring, pullbackColoring]

@[simp] theorem totalColoring_free_tail {kind : Kind}
    (ext : FiveExtension kind) (a : FiveVertex) (x : TailVertex) :
    totalColoring ext (freeVertex a) (tailVertex x) = ext.rows a x := by
  simp [totalColoring, pullbackColoring]

@[simp] theorem totalColoring_tail_tail {kind : Kind}
    (ext : FiveExtension kind) (x y : TailVertex) :
    totalColoring ext (tailVertex x) (tailVertex y) =
      ext.tail.coloring x y := by
  simp [totalColoring, pullbackColoring]

theorem totalColoring_noMono {kind : Kind} (ext : FiveExtension kind) :
    NoMonochromaticTriangle (totalColoring ext) := by
  apply noMono_pullback
    (joinColoring ext.inside ext.tail.coloring ext.rows)
    splitVertex splitVertex_injective
  exact (noMono_joinColoring_iff
    ext.inside ext.tail.coloring ext.rows).2
      ⟨ext.insideNoMono, ext.tail.noMono,
        ext.rowsAdmissible, ext.rowsPairCompatible⟩

/-! ## Relabeling the retained five rows -/

def transportFiveExtension {kind : Kind}
    (σ : Equiv.Perm FiveVertex) (ext : FiveExtension kind) :
    FiveExtension kind where
  tail := ext.tail
  inside := pullbackColoring ext.inside σ
  rows := fun a ↦ ext.rows (σ a)
  insideNoMono := noMono_pullback ext.inside σ σ.injective ext.insideNoMono
  insideRootForbidden := by
    intro a b hab
    exact ext.insideRootForbidden (σ a) (σ b) (σ.injective.ne hab)
  rowsAdmissible := fun a ↦ ext.rowsAdmissible (σ a)
  rowsPairCompatible := by
    intro a b hab x hbad
    exact ext.rowsPairCompatible (σ a) (σ b)
      (σ.injective.ne hab) x hbad

def transportDegreeFlooredFiveExtension {kind : Kind}
    (σ : Equiv.Perm FiveVertex) (ext : DegreeFlooredFiveExtension kind) :
    DegreeFlooredFiveExtension kind where
  toFiveExtension := transportFiveExtension σ ext.toFiveExtension
  zeroSupportLower := fun a ↦ ext.zeroSupportLower (σ a)
  zeroSupportUpper := fun a ↦ ext.zeroSupportUpper (σ a)
  nonzeroSupportLower := fun a q hq ↦ ext.nonzeroSupportLower (σ a) q hq
  nonzeroSupportUpper := fun a q hq ↦ ext.nonzeroSupportUpper (σ a) q hq

/-! ## A branch with the inside C5 orientation fixed -/

structure CanonicalBranch (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block)) where
  toDegreeFlooredFiveExtension : DegreeFlooredFiveExtension kind
  allFiveOwn : ∀ a : FiveVertex,
    toDegreeFlooredFiveExtension.toFiveExtension.rows a
        (blockVertex block position.val) = blockRootColor block
  insideCanonical : ∀ a b : FiveVertex, a ≠ b →
    toDegreeFlooredFiveExtension.toFiveExtension.inside a b =
      decodeRemainingColor block (!canonicalCycleWord.coloring a b)
  tailOwnDegreeLower :
    9 ≤ colorDegree
      toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val)
  tailOwnDegreeUpper :
    colorDegree
      toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockRootColor block) (blockVertex block position.val) ≤ 10

/-! Multiplication by two on the cyclic order sends the canonical five-cycle
to its complement.  The discovery pilot chose the first remaining colour on
the displayed cycle, whereas `canonicalCycleWord` calls those edges `true`
and `decodeRemainingColor` sends `true` to the second remaining colour.  This
fixed relabel makes the trusted formula use the pilot's exact orientation. -/

def cycleComplementPerm : Equiv.Perm FiveVertex where
  toFun := fun a => ![0, 2, 4, 1, 3] a
  invFun := fun a => ![0, 3, 1, 4, 2] a
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem canonicalCycleWord_cycleComplementPerm
    (a b : FiveVertex) (hab : a ≠ b) :
    canonicalCycleWord.coloring (cycleComplementPerm a)
        (cycleComplementPerm b) =
      !canonicalCycleWord.coloring a b := by
  fin_cases a <;> fin_cases b <;>
    simp [cycleComplementPerm, canonicalCycleWord,
      BoolK5Word.coloring] at hab ⊢

def CanonicalBranch.toFiveSupport {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    FiveSupportFiveRowExtension kind where
  toDegreeFlooredFiveExtension := branch.toDegreeFlooredFiveExtension
  block := block
  position := position
  allFiveOwn := branch.allFiveOwn
  tailOwnDegreeLower := branch.tailOwnDegreeLower
  tailOwnDegreeUpper := branch.tailOwnDegreeUpper

theorem exists_canonicalTransport {kind : Kind}
    (ext : FiveSupportFiveRowExtension kind) :
    Nonempty (CanonicalBranch kind ext.block ext.position) := by
  obtain ⟨σ, hσ⟩ := ext.exists_inside_cycle_relabel
  let combined : Equiv.Perm FiveVertex := cycleComplementPerm.trans σ
  let transported := transportDegreeFlooredFiveExtension combined
    ext.toDegreeFlooredFiveExtension
  refine ⟨{
    toDegreeFlooredFiveExtension := transported
    allFiveOwn := ?_
    insideCanonical := ?_
    tailOwnDegreeLower := ?_
    tailOwnDegreeUpper := ?_
  }⟩
  · intro a
    exact ext.allFiveOwn (combined a)
  · intro a b hab
    change ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
      (combined a) (combined b) = _
    calc
      ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (combined a) (combined b) =
        decodeRemainingColor ext.block
          (canonicalCycleWord.coloring (cycleComplementPerm a)
            (cycleComplementPerm b)) := by
              simpa [combined] using hσ
                (cycleComplementPerm a) (cycleComplementPerm b)
                (cycleComplementPerm.injective.ne hab)
      _ = decodeRemainingColor ext.block
          (!canonicalCycleWord.coloring a b) := by
            rw [canonicalCycleWord_cycleComplementPerm a b hab]
  · exact ext.tailOwnDegreeLower
  · exact ext.tailOwnDegreeUpper

theorem nonempty_fiveSupport_iff_exists_canonical (kind : Kind) :
    Nonempty (FiveSupportFiveRowExtension kind) ↔
      ∃ block : Fin 3, ∃ position : Fin (blockSize block),
        Nonempty (CanonicalBranch kind block position) := by
  constructor
  · rintro ⟨ext⟩
    exact ⟨ext.block, ext.position, exists_canonicalTransport ext⟩
  · rintro ⟨block, position, ⟨branch⟩⟩
    exact ⟨branch.toFiveSupport⟩

/-! ## Exact base formula -/

def blockTemplateUnitClauses (kind : Kind) (block : Fin 3) : Sat.Fmla :=
  (FiniteColorCNF.edges (blockSize block)).map fun pair =>
    [Sat.Literal.pos (edgeAtom
      (5 + blockStart block + pair.1)
      (5 + blockStart block + pair.2)
      (SingleRootStarCNF.canonicalPalette (Fin.succ block)
        (SingleRootStarCNF.templateColor
          (blockSize block) (kind.twisted block)
          pair.1 pair.2)).val)]

def templateUnitClauses (kind : Kind) : Sat.Fmla :=
  blockTemplateUnitClauses kind 0 ++
    blockTemplateUnitClauses kind 1 ++
      blockTemplateUnitClauses kind 2

def insideRootForbiddenUnitClauses : Sat.Fmla :=
  (FiniteColorCNF.edges 5).map fun pair =>
    [Sat.Literal.neg (edgeAtom pair.1 pair.2 0)]

def allFiveOwnUnitClauses (block : Fin 3)
    (position : Fin (blockSize block)) : Sat.Fmla :=
  (List.finRange 5).map fun a : FiveVertex =>
    [Sat.Literal.pos (edgeAtom a.val
      (5 + (blockVertex block position.val).val)
      (blockRootColor block).val)]

def canonicalInsideColorNat (block : Fin 3) (left right : Nat) : Fin 4 :=
  if hleft : left < 5 then
    if hright : right < 5 then
      decodeRemainingColor block
        (!canonicalCycleWord.coloring ⟨left, hleft⟩ ⟨right, hright⟩)
    else 0
  else 0

def insideC5UnitClauses (block : Fin 3) : Sat.Fmla :=
  (FiniteColorCNF.edges 5).map fun pair =>
    [Sat.Literal.pos (edgeAtom pair.1 pair.2
      (canonicalInsideColorNat block pair.1 pair.2).val)]

/-- Authoritative non-counter prefix.  Clause order is the good-colouring
base, tail units, root-forbidden units, five selected-column units, then ten
canonical C5 units. -/
def baseFmla (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block)) : Sat.Fmla :=
  FiniteColorCNF.goodColoringFmla 51 4 ++
    templateUnitClauses kind ++
      insideRootForbiddenUnitClauses ++
        allFiveOwnUnitClauses block position ++
          insideC5UnitClauses block

private theorem canonicalBranch_satisfies_blockTemplateUnitClauses
    {kind : Kind} {selectedBlock : Fin 3}
    {position : Fin (blockSize selectedBlock)}
    (branch : CanonicalBranch kind selectedBlock position)
    (block : Fin 3) :
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)).satisfies_fmla
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
  let q : Fin 4 := SingleRootStarCNF.canonicalPalette (Fin.succ block)
    (SingleRootStarCNF.templateColor
      (blockSize block) (kind.twisted block)
      pair.1 pair.2)
  have hleftVal : left.val = 5 + blockStart block + pair.1 := by
    simp [left, leftTail, tailVertex, blockVertex_val block hleft]
    omega
  have hrightVal : right.val = 5 + blockStart block + pair.2 := by
    simp [right, rightTail, tailVertex, blockVertex_val block hright]
    omega
  apply satisfies_of_mem_holds
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension))
    (l := Sat.Literal.pos (edgeAtom
      (5 + blockStart block + pair.1)
      (5 + blockStart block + pair.2) q.val))
  · exact List.Mem.head _
  · change coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)
      (edgeAtom
        (5 + blockStart block + pair.1)
        (5 + blockStart block + pair.2) q.val)
    rw [← hleftVal, ← hrightVal, coloringValuation_edgeAtom]
    change totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
      (tailVertex leftTail) (tailVertex rightTail) = q
    rw [totalColoring_tail_tail]
    exact branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.templateCanonical
      block pair.1 pair.2 hleft hright hlr

theorem canonicalBranch_satisfies_templateUnitClauses
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)).satisfies_fmla
        (templateUnitClauses kind) := by
  constructor
  intro clause hclause
  simp only [templateUnitClauses, List.mem_append] at hclause
  rcases hclause with (hzero | hone) | htwo
  · exact (canonicalBranch_satisfies_blockTemplateUnitClauses branch 0).prop
      clause hzero
  · exact (canonicalBranch_satisfies_blockTemplateUnitClauses branch 1).prop
      clause hone
  · exact (canonicalBranch_satisfies_blockTemplateUnitClauses branch 2).prop
      clause htwo

theorem canonicalBranch_satisfies_insideRootForbiddenUnitClauses
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)).satisfies_fmla
        insideRootForbiddenUnitClauses := by
  constructor
  intro clause hclause
  simp only [insideRootForbiddenUnitClauses, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  obtain ⟨hleft, hright, hlr⟩ :=
    SingleRootStarCNF.mem_edges_bounds hpair
  let left : FiveVertex := ⟨pair.1, hleft⟩
  let right : FiveVertex := ⟨pair.2, hright⟩
  apply satisfies_of_mem_holds
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension))
    (l := Sat.Literal.neg (edgeAtom pair.1 pair.2 0))
  · exact List.Mem.head _
  · change ¬coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)
      (edgeAtom (freeVertex left).val (freeVertex right).val (0 : Fin 4).val)
    rw [coloringValuation_edgeAtom, totalColoring_free_free]
    exact branch.toDegreeFlooredFiveExtension.toFiveExtension.insideRootForbidden
      left right (Fin.ne_of_lt hlr)

theorem canonicalBranch_satisfies_allFiveOwnUnitClauses
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)).satisfies_fmla
        (allFiveOwnUnitClauses block position) := by
  constructor
  intro clause hclause
  simp only [allFiveOwnUnitClauses, List.mem_map] at hclause
  obtain ⟨a, _ha, rfl⟩ := hclause
  let selected : TailVertex := blockVertex block position.val
  apply satisfies_of_mem_holds
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension))
    (l := Sat.Literal.pos (edgeAtom a.val (5 + selected.val)
      (blockRootColor block).val))
  · exact List.Mem.head _
  · change coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)
      (edgeAtom (freeVertex a).val (tailVertex selected).val
        (blockRootColor block).val)
    rw [coloringValuation_edgeAtom, totalColoring_free_tail]
    exact branch.allFiveOwn a

theorem canonicalBranch_satisfies_insideC5UnitClauses
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)).satisfies_fmla
        (insideC5UnitClauses block) := by
  constructor
  intro clause hclause
  simp only [insideC5UnitClauses, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  obtain ⟨hleft, hright, hlr⟩ :=
    SingleRootStarCNF.mem_edges_bounds hpair
  let left : FiveVertex := ⟨pair.1, hleft⟩
  let right : FiveVertex := ⟨pair.2, hright⟩
  let q : Fin 4 := canonicalInsideColorNat block pair.1 pair.2
  apply satisfies_of_mem_holds
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension))
    (l := Sat.Literal.pos (edgeAtom pair.1 pair.2 q.val))
  · exact List.Mem.head _
  · change coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)
      (edgeAtom (freeVertex left).val (freeVertex right).val q.val)
    rw [coloringValuation_edgeAtom, totalColoring_free_free]
    simpa [q, canonicalInsideColorNat, hleft, hright, left, right] using
      (branch.insideCanonical left right (Fin.ne_of_lt hlr))

theorem canonicalBranch_satisfies_baseFmla
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)).satisfies_fmla
        (baseFmla kind block position) := by
  constructor
  intro clause hclause
  simp only [baseFmla, List.mem_append] at hclause
  rcases hclause with ((((hgood | htemplate) | hforbidden) | hown) | hc5)
  · exact (coloring_satisfies_goodColoringFmla _
      (totalColoring_noMono
        branch.toDegreeFlooredFiveExtension.toFiveExtension)).prop
      clause hgood
  · exact (canonicalBranch_satisfies_templateUnitClauses branch).prop
      clause htemplate
  · exact
      (canonicalBranch_satisfies_insideRootForbiddenUnitClauses branch).prop
        clause hforbidden
  · exact (canonicalBranch_satisfies_allFiveOwnUnitClauses branch).prop
      clause hown
  · exact (canonicalBranch_satisfies_insideC5UnitClauses branch).prop
      clause hc5

/-! ## Exact 42-counter family -/

abbrev CounterPhase := Fin 2

def upperPhase : CounterPhase := 0
def lowerPhase : CounterPhase := 1

inductive CounterContext where
  | row (a : FiveVertex) (q : Fin 4) (phase : CounterPhase)
  | selectedTail (phase : CounterPhase)
  deriving DecidableEq, Fintype, Repr

def contextOfIndex (i : Fin 42) : CounterContext :=
  if h : i.val < 40 then
    .row ⟨i.val / 8, by omega⟩
      ⟨(i.val % 8) / 2, by omega⟩ ⟨i.val % 2, by omega⟩
  else
    .selectedTail ⟨i.val - 40, by omega⟩

def counterContexts : List CounterContext :=
  (List.finRange 42).map contextOfIndex

theorem counterContexts_length : counterContexts.length = 42 := by
  simp [counterContexts]

/-- Contexts `0,...,39` are row/colour/phase; `40,41` are the sharp selected
tail endpoint upper/lower counters. -/
def contextIndex : CounterContext → Nat
  | .row a q phase => (a.val * 4 + q.val) * 2 + phase.val
  | .selectedTail phase => 40 + phase.val

@[simp] theorem contextIndex_contextOfIndex (i : Fin 42) :
    contextIndex (contextOfIndex i) = i.val := by
  by_cases h : i.val < 40
  · simp only [contextOfIndex, h, dite_true, contextIndex]
    omega
  · simp only [contextOfIndex, h, dite_false, contextIndex]
    omega

theorem contextOfIndex_injective : Function.Injective contextOfIndex := by
  intro i j hij
  apply Fin.ext
  have h := congrArg contextIndex hij
  simpa using h

theorem counterContexts_nodup : counterContexts.Nodup := by
  exact (List.nodup_finRange 42).map contextOfIndex_injective

theorem contextIndex_lt (context : CounterContext) :
    contextIndex context < 42 := by
  cases context with
  | row a q phase =>
      simp only [contextIndex]
      omega
  | selectedTail phase =>
      simp only [contextIndex]
      omega

/-! The sequential-counter tags intentionally use the exact synthetic
`Fin 52` layout of `ExportProfileDFiveCommonC5Pilot`: a row counter reserves
vertex `2 * row + phase` and its actual colour, while the two selected-tail
counters reserve vertices ten and eleven with synthetic colour one.  The
selected-tail colour in the tag is only a namespace coordinate; its semantic
input colour remains the selected block's own colour. -/

abbrev CounterNamespaceVertex := Fin 52

def namespaceVertex : CounterContext → CounterNamespaceVertex
  | .row a _ phase => ⟨a.val * 2 + phase.val, by omega⟩
  | .selectedTail phase => ⟨10 + phase.val, by omega⟩

def namespaceColor : CounterContext → Fin 4
  | .row _ q _ => q
  | .selectedTail _ => 1

theorem contextIndex_injective : Function.Injective contextIndex := by
  intro left right hval
  cases left with
  | row a q phase =>
      cases right with
      | row b r otherPhase =>
          have ha : a.val = b.val := by
            simp only [contextIndex] at hval
            omega
          have hq : q.val = r.val := by
            simp only [contextIndex] at hval
            omega
          have hp : phase.val = otherPhase.val := by
            simp only [contextIndex] at hval
            omega
          cases Fin.ext ha
          cases Fin.ext hq
          cases Fin.ext hp
          rfl
      | selectedTail otherPhase =>
          simp only [contextIndex] at hval
          omega
  | selectedTail phase =>
      cases right with
      | row b r otherPhase =>
          simp only [contextIndex] at hval
          omega
      | selectedTail otherPhase =>
          have hp : phase.val = otherPhase.val := by
            simp only [contextIndex] at hval
            omega
          cases Fin.ext hp
          rfl

theorem contextOfIndex_contextIndex (context : CounterContext) :
    contextOfIndex ⟨contextIndex context, contextIndex_lt context⟩ =
      context := by
  apply contextIndex_injective
  exact contextIndex_contextOfIndex _

theorem mem_counterContexts (context : CounterContext) :
    context ∈ counterContexts := by
  apply List.mem_map.mpr
  refine ⟨⟨contextIndex context, contextIndex_lt context⟩,
    List.mem_finRange _, ?_⟩
  exact contextOfIndex_contextIndex context

def counterTag (context : CounterContext) : Nat :=
  OutsideDegreeCapCNF.outsideDegreeCounterTag
    (namespaceVertex context) (namespaceColor context)

theorem counterTag_injective : Function.Injective counterTag := by
  intro left right h
  obtain ⟨hvertex, hcolor⟩ :=
    OutsideDegreeCapCNF.outsideDegreeCounterTag_injective h
  cases left with
  | row a q phase =>
      cases right with
      | row b r otherPhase =>
          have ha : a = b := by
            have hval := congrArg Fin.val hvertex
            simp only [namespaceVertex] at hval
            apply Fin.ext
            omega
          have hp : phase = otherPhase := by
            have hval := congrArg Fin.val hvertex
            simp only [namespaceVertex] at hval
            apply Fin.ext
            omega
          have hq : q = r := by
            simpa only [namespaceColor] using hcolor
          cases ha
          cases hq
          cases hp
          rfl
      | selectedTail otherPhase =>
          have hval := congrArg Fin.val hvertex
          simp only [namespaceVertex] at hval
          omega
  | selectedTail phase =>
      cases right with
      | row b r otherPhase =>
          have hval := congrArg Fin.val hvertex
          simp only [namespaceVertex] at hval
          omega
      | selectedTail otherPhase =>
          have hp : phase = otherPhase := by
            have hval := congrArg Fin.val hvertex
            simp only [namespaceVertex] at hval
            apply Fin.ext
            omega
          cases hp
          rfl

def rowColorAtoms (a : FiveVertex) (q : Fin 4) : List Nat :=
  (List.finRange 46).map fun x : TailVertex =>
    edgeAtom a.val (5 + x.val) q.val

def otherColors (q : Fin 4) : List (Fin 4) :=
  (List.finRange 4).filter fun r => r ≠ q

@[simp] theorem otherColors_zero : otherColors (0 : Fin 4) = [1, 2, 3] := by
  decide

@[simp] theorem otherColors_one : otherColors (1 : Fin 4) = [0, 2, 3] := by
  decide

@[simp] theorem otherColors_two : otherColors (2 : Fin 4) = [0, 1, 3] := by
  decide

@[simp] theorem otherColors_three : otherColors (3 : Fin 4) = [0, 1, 2] := by
  decide

def rowOtherColorAtoms (a : FiveVertex) (q : Fin 4) : List Nat :=
  (otherColors q).flatMap fun r => rowColorAtoms a r

def selectedTailVertex (block : Fin 3)
    (position : Fin (blockSize block)) : TailVertex :=
  blockVertex block position.val

def selectedTailColorAtoms (block : Fin 3)
    (position : Fin (blockSize block)) (q : Fin 4) : List Nat :=
  ((List.finRange 46).filter fun y : TailVertex =>
      y ≠ selectedTailVertex block position).map fun y =>
    OutsideDegreeCapCNF.outsideIncidentEdgeAtom
      (tailVertex (selectedTailVertex block position)) (tailVertex y) q

def selectedTailOtherColorAtoms (block : Fin 3)
    (position : Fin (blockSize block)) : List Nat :=
  (otherColors (blockRootColor block)).flatMap fun q =>
    selectedTailColorAtoms block position q

def supportUpperBound (q : Fin 4) : Nat :=
  if q = 0 then 15 else 13

def complementaryUpperBound (q : Fin 4) : Nat :=
  if q = 0 then 35 else 39

def contextBound : CounterContext → Nat
  | .row _ q phase =>
      if phase = upperPhase then supportUpperBound q
      else complementaryUpperBound q
  | .selectedTail phase =>
      if phase = upperPhase then 10 else 36

def contextInputs (block : Fin 3) (position : Fin (blockSize block)) :
    CounterContext → List Nat
  | .row a q phase =>
      if phase = upperPhase then rowColorAtoms a q
      else rowOtherColorAtoms a q
  | .selectedTail phase =>
      if phase = upperPhase then
        selectedTailColorAtoms block position (blockRootColor block)
      else selectedTailOtherColorAtoms block position

def counterSpec (block : Fin 3) (position : Fin (blockSize block))
    (context : CounterContext) : CounterSpec where
  tag := counterTag context
  bound := contextBound context
  inputs := contextInputs block position context

def counterSpecs (block : Fin 3)
    (position : Fin (blockSize block)) : List CounterSpec :=
  counterContexts.map (counterSpec block position)

theorem counterSpecs_length (block : Fin 3)
    (position : Fin (blockSize block)) :
    (counterSpecs block position).length = 42 := by
  simp [counterSpecs, counterContexts_length]

theorem counterSpecs_tags_nodup (block : Fin 3)
    (position : Fin (blockSize block)) :
    ((counterSpecs block position).map CounterSpec.tag).Nodup := by
  unfold counterSpecs
  rw [List.map_map]
  exact counterContexts_nodup.map counterTag_injective

/-! ## Exact mathematical input counts -/

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

theorem trueInputCount_rowColorAtoms {kind : Kind}
    (ext : FiveExtension kind) (a : FiveVertex) (q : Fin 4) :
    trueInputCount (coloringValuation (totalColoring ext))
        (rowColorAtoms a q) =
      (rowColorSupport (ext.rows a) q).card := by
  unfold trueInputCount rowColorAtoms
  rw [List.countP_map]
  have hbits :
      (truthBit (coloringValuation (totalColoring ext)) ∘
          fun x : TailVertex => edgeAtom a.val (5 + x.val) q.val) =
        (fun x : TailVertex => decide (ext.rows a x = q)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, truthBit_eq_true, decide_eq_true_eq]
    change coloringValuation (totalColoring ext)
        (edgeAtom (freeVertex a).val (tailVertex x).val q.val) ↔
      ext.rows a x = q
    rw [coloringValuation_edgeAtom, totalColoring_free_tail]
  rw [hbits]
  exact count_finRange_eq_rowColorSupport (ext.rows a) q

private theorem trueInputCount_flatMap
    (v : Sat.Valuation) {A : Type*} (contexts : List A)
    (inputs : A → List Nat) :
    trueInputCount v (contexts.flatMap inputs) =
      (contexts.map fun context => trueInputCount v (inputs context)).sum := by
  simp [trueInputCount, List.countP_flatMap, Function.comp_def]

theorem trueInputCount_rowOtherColorAtoms {kind : Kind}
    (ext : FiveExtension kind) (a : FiveVertex) (q : Fin 4) :
    trueInputCount (coloringValuation (totalColoring ext))
        (rowOtherColorAtoms a q) =
      46 - (rowColorSupport (ext.rows a) q).card := by
  have hsum := ProfileDRowSupportBounds61.rowColorSupport_sum_fin4
    (ext.rows a)
  simp only [TailVertex, Fintype.card_fin] at hsum
  rw [rowOtherColorAtoms, trueInputCount_flatMap]
  fin_cases q <;>
    simp [trueInputCount_rowColorAtoms] <;> omega

theorem tailVertex_injective : Function.Injective tailVertex := by
  intro x y h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [tailVertex] at hval
  omega

private theorem countP_eq_of_pointwise_on_list
    {A : Type*} (f g : A → Bool) : ∀ list : List A,
    (∀ x ∈ list, f x = g x) →
      List.countP f list = List.countP g list
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.countP_cons, List.countP_cons,
        h x (List.Mem.head xs)]
      rw [countP_eq_of_pointwise_on_list f g xs
        (fun y hy => h y (List.Mem.tail x hy))]

theorem trueInputCount_selectedTailColorAtoms {kind : Kind}
    (ext : FiveExtension kind) (block : Fin 3)
    (position : Fin (blockSize block)) (q : Fin 4) :
    trueInputCount (coloringValuation (totalColoring ext))
        (selectedTailColorAtoms block position q) =
      colorDegree ext.tail.coloring q
        (selectedTailVertex block position) := by
  let selected := selectedTailVertex block position
  let candidates := (List.finRange 46).filter fun y : TailVertex => y ≠ selected
  let atom : TailVertex → Nat := fun y =>
    OutsideDegreeCapCNF.outsideIncidentEdgeAtom
      (tailVertex selected) (tailVertex y) q
  let actual : TailVertex → Bool := fun y =>
    decide (ext.tail.coloring selected y = q)
  unfold trueInputCount selectedTailColorAtoms
  rw [List.countP_map]
  change List.countP
      (truthBit (coloringValuation (totalColoring ext)) ∘ atom)
      candidates = _
  rw [countP_eq_of_pointwise_on_list _ actual candidates (by
    intro y hy
    have hyne : y ≠ selected :=
      of_decide_eq_true (List.mem_filter.mp hy).2
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, truthBit_eq_true, actual,
      decide_eq_true_eq]
    rw [OutsideDegreeCapCNF.coloringValuation_outsideIncidentEdgeAtom
      (totalColoring ext) (tailVertex selected) (tailVertex y)
      (tailVertex_injective.ne hyne.symm) q]
    rw [totalColoring_tail_tail])]
  rw [List.countP_eq_length_filter]
  have hlists :
      candidates.filter actual =
        OutsideDegreeCapCNF.outsideColorNeighborList
          ext.tail.coloring selected q := by
    simp [candidates, actual,
      OutsideDegreeCapCNF.outsideColorNeighborList,
      List.filter_filter, Bool.and_comm]
  rw [hlists, OutsideDegreeCapCNF.outsideColorNeighborList_length]

theorem trueInputCount_selectedTailOtherColorAtoms {kind : Kind}
    (ext : FiveExtension kind) (block : Fin 3)
    (position : Fin (blockSize block)) :
    trueInputCount (coloringValuation (totalColoring ext))
        (selectedTailOtherColorAtoms block position) =
      45 - colorDegree ext.tail.coloring (blockRootColor block)
        (selectedTailVertex block position) := by
  have hsum := sum_colorDegree_eq_card_sub_one ext.tail.coloring
    (selectedTailVertex block position)
  have hcard : Fintype.card TailVertex = 46 := by decide
  rw [Fin.sum_univ_four] at hsum
  simp only [hcard] at hsum
  rw [selectedTailOtherColorAtoms, trueInputCount_flatMap]
  generalize hq : blockRootColor block = q
  fin_cases q <;>
    simp [trueInputCount_selectedTailColorAtoms] <;> omega

end ProfileDHighOwnFiveSupportC5CNF
end R4333
