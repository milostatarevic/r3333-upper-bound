import R4333Lean.CheckedLRAT
import R4333Lean.Basic
import Mathlib.Data.Nat.Pairing

/-!
# A semantic CNF boundary for finite edge-colourings

This file is the reusable trusted boundary between a mathematical
`EdgeColoring` and LRAT-refutable finite formulas.  Variable identities are
defined in Lean using `Nat.pair`; no external variable map is trusted.

The base formula says that every unordered edge has exactly one colour and
that no triple is monochromatic.  Later attaching-case formulas can append
unit clauses, embedding circuits, and auxiliary definitions to this base.
-/

namespace R4333

namespace FiniteColorCNF

/-- The proposition asserted by a SAT literal. -/
def Holds (v : Sat.Valuation) : Sat.Literal → Prop
  | .pos i => v i
  | .neg i => ¬v i

theorem holds_not_neg (v : Sat.Valuation) (l : Sat.Literal) :
    Holds v l → v.neg l → False := by
  cases l <;> simp [Holds, Sat.Valuation.neg]

/-- Convert a literal list using the public clause constructors.  Keeping
this recursion explicit avoids relying on elaborator transparency for
`Sat.Clause`, which is intentionally a named definition in Mathlib. -/
def clauseOfList : List Sat.Literal → Sat.Clause
  | [] => Sat.Clause.nil
  | l :: ls => Sat.Clause.cons l (clauseOfList ls)

theorem clauseOfList_eq (clause : List Sat.Literal) :
    clauseOfList clause = (show Sat.Clause from clause) := by
  induction clause with
  | nil => rfl
  | cons l ls ih =>
      simp only [clauseOfList, Sat.Clause.cons]
      rw [ih]

private theorem satisfies_clauseOfList_of_mem_holds
    (v : Sat.Valuation) {clause : List Sat.Literal} {l : Sat.Literal}
    (hl : List.Mem l clause) (htrue : Holds v l) :
    v.satisfies (clauseOfList clause) := by
  induction clause generalizing l with
  | nil => exact nomatch hl
  | cons head tail ih =>
      change v.neg head → v.satisfies (clauseOfList tail)
      intro hfalse
      cases hl with
      | head => exact (holds_not_neg v _ htrue hfalse).elim
      | tail _ hl => exact ih hl htrue

/-- A clause is satisfied if any one of its literals is known true. -/
theorem satisfies_of_mem_holds
    (v : Sat.Valuation) {clause : List Sat.Literal} {l : Sat.Literal}
    (hl : List.Mem l clause) (htrue : Holds v l) :
    v.satisfies (show Sat.Clause from clause) := by
  rw [← clauseOfList_eq clause]
  exact satisfies_clauseOfList_of_mem_holds v hl htrue

/-- Pairing-based variable number for the assertion that edge `a-b` has
colour `q`.  Attaching encoders may use disjoint tagged namespaces by
pairing an additional leading tag. -/
def edgeAtom (a b q : Nat) : Nat := Nat.pair (Nat.pair a b) q

/-- Decode an edge atom against a concrete finite colouring.  Numbers that
do not decode to in-range vertices and colours are false. -/
def coloringValuation {n k : Nat}
    (c : EdgeColoring (Fin n) (Fin k)) : Sat.Valuation := fun atom =>
  let outer := Nat.unpair atom
  let vertices := Nat.unpair outer.1
  if ha : vertices.1 < n then
    if hb : vertices.2 < n then
      if hq : outer.2 < k then
        c ⟨vertices.1, ha⟩ ⟨vertices.2, hb⟩ = ⟨outer.2, hq⟩
      else False
    else False
  else False

@[simp]
theorem coloringValuation_edgeAtom {n k : Nat}
    (c : EdgeColoring (Fin n) (Fin k))
    (a b : Fin n) (q : Fin k) :
    coloringValuation c (edgeAtom a b q) ↔ c a b = q := by
  simp [coloringValuation, edgeAtom, Nat.unpair_pair]

/-- Naturals `0,...,n-1`, used to keep the generated clause order explicit. -/
def vertices (n : Nat) : List Nat := List.range n

/-- Lexicographically ordered pairs `a<b`, matching the conventional
DIMACS edge order. -/
def edges (n : Nat) : List (Nat × Nat) :=
  (vertices n).flatMap fun a =>
    ((vertices n).filter fun b => a < b).map fun b => (a, b)

/-- Lexicographically ordered triples `a<b<c`. -/
def triples (n : Nat) : List (Nat × Nat × Nat) :=
  (vertices n).flatMap fun a =>
    ((vertices n).filter fun b => a < b).flatMap fun b =>
      ((vertices n).filter fun d => b < d).map fun d => (a, b, d)

/-- Every edge receives at least one colour. -/
def atLeastOneClauses (n k : Nat) : Sat.Fmla :=
  (edges n).map fun e =>
    (List.range k).map fun q => Sat.Literal.pos (edgeAtom e.1 e.2 q)

/-- No edge receives two distinct colours. -/
def atMostOneClauses (n k : Nat) : Sat.Fmla :=
  (edges n).flatMap fun e =>
    (edges k).map fun qr =>
      [Sat.Literal.neg (edgeAtom e.1 e.2 qr.1),
       Sat.Literal.neg (edgeAtom e.1 e.2 qr.2)]

/-- No triple has all three edges in one colour. -/
def triangleClauses (n k : Nat) : Sat.Fmla :=
  (triples n).flatMap fun t =>
    (List.range k).map fun q =>
      [Sat.Literal.neg (edgeAtom t.1 t.2.1 q),
       Sat.Literal.neg (edgeAtom t.1 t.2.2 q),
       Sat.Literal.neg (edgeAtom t.2.1 t.2.2 q)]

/-- Canonical CNF for a triangle-free `k`-edge-colouring of `K_n`. -/
def goodColoringFmla (n k : Nat) : Sat.Fmla :=
  atLeastOneClauses n k ++ atMostOneClauses n k ++ triangleClauses n k

private theorem mem_vertices_lt {n a : Nat} (h : a ∈ vertices n) : a < n := by
  simpa [vertices] using h

private theorem edge_members_lt {n a b : Nat} (h : (a, b) ∈ edges n) :
    a < n ∧ b < n ∧ a < b := by
  simp only [edges, List.mem_flatMap, List.mem_map] at h
  obtain ⟨a', ha', b', hb', hp⟩ := h
  have ha'lt : a' < n := by simpa [vertices] using ha'
  have hb'mem : b' ∈ vertices n := (List.mem_filter.mp hb').1
  have hb'lt : b' < n := by simpa [vertices] using hb'mem
  have hab' : a' < b' := of_decide_eq_true (List.mem_filter.mp hb').2
  injection hp with haa hbb
  subst a'
  subst b'
  exact ⟨ha'lt, hb'lt, hab'⟩

/-- An in-range strictly ordered pair occurs in the canonical edge list. -/
theorem mem_edges_of_bounds {n a b : Nat}
    (ha : a < n) (hb : b < n) (hab : a < b) :
    (a, b) ∈ edges n := by
  simp only [edges, List.mem_flatMap, List.mem_map]
  refine ⟨a, ?_, b, ?_, rfl⟩
  · simpa [vertices] using ha
  · exact List.mem_filter.mpr ⟨by simpa [vertices] using hb, by simpa using hab⟩

private theorem triple_members_lt {n a b d : Nat}
    (h : (a, b, d) ∈ triples n) :
    a < n ∧ b < n ∧ d < n ∧ a < b ∧ b < d := by
  simp only [triples, List.mem_flatMap, List.mem_map] at h
  obtain ⟨a', ha', b', hb', d', hd', hp⟩ := h
  have ha'lt : a' < n := by simpa [vertices] using ha'
  have hb'mem : b' ∈ vertices n := (List.mem_filter.mp hb').1
  have hb'lt : b' < n := by simpa [vertices] using hb'mem
  have hab' : a' < b' := of_decide_eq_true (List.mem_filter.mp hb').2
  have hd'mem : d' ∈ vertices n := (List.mem_filter.mp hd').1
  have hd'lt : d' < n := by simpa [vertices] using hd'mem
  have hbd' : b' < d' := of_decide_eq_true (List.mem_filter.mp hd').2
  simp only [Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩
  exact ⟨ha'lt, hb'lt, hd'lt, hab', hbd'⟩

/-- Public bounds/ordering interface for a generated canonical triple. -/
theorem mem_triples_iff_bounds {n a b d : Nat}
    (h : (a, b, d) ∈ triples n) :
    a < n ∧ b < n ∧ d < n ∧ a < b ∧ b < d :=
  triple_members_lt h

private theorem satisfies_atLeastOne {n k : Nat}
    (c : EdgeColoring (Fin n) (Fin k)) :
    (coloringValuation c).satisfies_fmla (atLeastOneClauses n k) := by
  constructor
  intro clause hclause
  simp only [atLeastOneClauses, List.mem_map] at hclause
  obtain ⟨⟨a, b⟩, hedge, rfl⟩ := hclause
  obtain ⟨ha, hb, -⟩ := edge_members_lt hedge
  let a' : Fin n := ⟨a, ha⟩
  let b' : Fin n := ⟨b, hb⟩
  let q : Fin k := c a' b'
  apply satisfies_of_mem_holds (coloringValuation c)
    (l := Sat.Literal.pos (edgeAtom a b q))
  · change List.Mem (Sat.Literal.pos (edgeAtom a b q))
      ((List.range k).map fun r => Sat.Literal.pos (edgeAtom a b r))
    exact List.mem_map.mpr ⟨q, List.mem_range.mpr q.isLt, rfl⟩
  · simpa [Holds, a', b'] using
      (coloringValuation_edgeAtom c a' b' q).2 rfl

private theorem satisfies_atMostOne {n k : Nat}
    (c : EdgeColoring (Fin n) (Fin k)) :
    (coloringValuation c).satisfies_fmla (atMostOneClauses n k) := by
  constructor
  intro clause hclause
  simp only [atMostOneClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨⟨a, b⟩, hedge, ⟨⟨q, r⟩, hqr, rfl⟩⟩ := hclause
  obtain ⟨ha, hb, -⟩ := edge_members_lt hedge
  obtain ⟨hq, hr, hne⟩ := edge_members_lt hqr
  let a' : Fin n := ⟨a, ha⟩
  let b' : Fin n := ⟨b, hb⟩
  let q' : Fin k := ⟨q, hq⟩
  let r' : Fin k := ⟨r, hr⟩
  have hqrne : q' ≠ r' := by
    apply Fin.ne_of_lt
    exact hne
  by_cases hcq : c a' b' = q'
  · apply satisfies_of_mem_holds (coloringValuation c)
        (l := Sat.Literal.neg (edgeAtom a b r))
        (List.Mem.tail _ (List.Mem.head _))
    change ¬coloringValuation c (edgeAtom a b r)
    have hatom : edgeAtom a b r = edgeAtom a' b' r' := rfl
    rw [hatom, coloringValuation_edgeAtom]
    intro hcr
    exact hqrne (hcq.symm.trans hcr)
  · apply satisfies_of_mem_holds (coloringValuation c)
        (l := Sat.Literal.neg (edgeAtom a b q)) (List.Mem.head _)
    change ¬coloringValuation c (edgeAtom a b q)
    have hatom : edgeAtom a b q = edgeAtom a' b' q' := rfl
    rw [hatom, coloringValuation_edgeAtom]
    exact hcq

private theorem satisfies_triangles {n k : Nat}
    (c : EdgeColoring (Fin n) (Fin k))
    (hc : NoMonochromaticTriangle c) :
    (coloringValuation c).satisfies_fmla (triangleClauses n k) := by
  constructor
  intro clause hclause
  simp only [triangleClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨⟨a, b, d⟩, htriple, ⟨q, hq, rfl⟩⟩ := hclause
  have hq' : q < k := List.mem_range.mp hq
  obtain ⟨ha, hb, hd, hab, hbd⟩ := triple_members_lt htriple
  let a' : Fin n := ⟨a, ha⟩
  let b' : Fin n := ⟨b, hb⟩
  let d' : Fin n := ⟨d, hd⟩
  let q' : Fin k := ⟨q, hq'⟩
  have hdistinct : PairwiseDistinct a' b' d' := by
    exact ⟨Fin.ne_of_lt hab, Fin.ne_of_lt (hab.trans hbd), Fin.ne_of_lt hbd⟩
  have hnot : ¬(c a' b' = q' ∧ c a' d' = q' ∧ c b' d' = q') := by
    rintro ⟨habq, hadq, hbdq⟩
    apply hc a' b' d' hdistinct
    exact ⟨habq.trans hadq.symm, hadq.trans hbdq.symm⟩
  by_cases habq : c a' b' = q'
  · by_cases hadq : c a' d' = q'
    · apply satisfies_of_mem_holds (coloringValuation c)
          (l := Sat.Literal.neg (edgeAtom b d q))
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      change ¬coloringValuation c (edgeAtom b d q)
      have hatom : edgeAtom b d q = edgeAtom b' d' q' := rfl
      rw [hatom, coloringValuation_edgeAtom]
      intro h
      exact hnot ⟨habq, hadq, h⟩
    · apply satisfies_of_mem_holds (coloringValuation c)
          (l := Sat.Literal.neg (edgeAtom a d q))
          (List.Mem.tail _ (List.Mem.head _))
      change ¬coloringValuation c (edgeAtom a d q)
      have hatom : edgeAtom a d q = edgeAtom a' d' q' := rfl
      rw [hatom, coloringValuation_edgeAtom]
      exact hadq
  · apply satisfies_of_mem_holds (coloringValuation c)
        (l := Sat.Literal.neg (edgeAtom a b q)) (List.Mem.head _)
    change ¬coloringValuation c (edgeAtom a b q)
    have hatom : edgeAtom a b q = edgeAtom a' b' q' := rfl
    rw [hatom, coloringValuation_edgeAtom]
    exact habq

/-- The central semantic bridge: every mathematical good colouring yields a
valuation satisfying the Lean-generated base CNF. -/
theorem coloring_satisfies_goodColoringFmla {n k : Nat}
    (c : EdgeColoring (Fin n) (Fin k))
    (hc : NoMonochromaticTriangle c) :
    (coloringValuation c).satisfies_fmla (goodColoringFmla n k) := by
  refine ⟨?_⟩
  intro clause hclause
  simp only [goodColoringFmla, List.mem_append] at hclause
  rcases hclause with (hclause | hclause) | hclause
  · exact (satisfies_atLeastOne c).prop clause hclause
  · exact (satisfies_atMostOne c).prop clause hclause
  · exact (satisfies_triangles c hc).prop clause hclause

/-- An LRAT refutation of the canonical base CNF rules out a mathematical
good colouring with no additional trust assumptions. -/
theorem no_good_coloring_of_lrat {n k : Nat}
    (hunsat : (goodColoringFmla n k).proof []) :
    ¬∃ c : EdgeColoring (Fin n) (Fin k), NoMonochromaticTriangle c := by
  rintro ⟨c, hc⟩
  exact hunsat (coloringValuation c) (coloring_satisfies_goodColoringFmla c hc)

#print axioms R4333.FiniteColorCNF.coloring_satisfies_goodColoringFmla
#print axioms R4333.FiniteColorCNF.no_good_coloring_of_lrat

end FiniteColorCNF

end R4333
