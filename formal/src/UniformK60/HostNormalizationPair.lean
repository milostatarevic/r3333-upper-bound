import UniformK60.HostNormalization
import UniformK60.Reduction

set_option autoImplicit false
namespace UniformK60.HostNormalization
open Ramsey61 Finset UniformK60.Physical

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The common pair is named by a single permutation of the four host colors. -/
theorem high_pair_palette : ∀ high : Finset FourColor, high.card = 2 →
    ∃ σ : Equiv.Perm FourColor,
      ∀ q : Color, (σ (palette q) ∈ high ↔ q.val < 2) := by decide

/-- Generic upper bounds; vertices may have either C profile. -/
def NamedCaps (c : Host) : Prop :=
  ∀ v : Vertex, ∀ q : Color, colorDegree c (palette q) v ≤ if q.val < 2 then 16 else 14

def NamedPair (c : Host) : Prop :=
  ∀ v : Vertex, ∀ q : Color, (15 ≤ colorDegree c (palette q) v ↔ q.val < 2)

/-- Naming the common pair preserves the original physical host and all colors
through one global palette permutation, with no low-degree equalities added. -/
theorem common_pair_to_named (c : Host) (hc : NoMonochromaticTriangle c)
    (hp : CommonCriticalPair c) :
    ∃ σ : Equiv.Perm FourColor,
      NoMonochromaticTriangle (relabel c (Equiv.refl _) σ) ∧
      NamedCaps (relabel c (Equiv.refl _) σ) ∧
      NamedPair (relabel c (Equiv.refl _) σ) := by
  classical
  obtain ⟨high, hcard, hhigh⟩ := hp
  obtain ⟨σ, hσ⟩ := high_pair_palette high hcard
  have hn : NamedPair (relabel c (Equiv.refl _) σ) := by
    intro v q
    rw [relabel_degree]
    change 15 ≤ colorDegree c (σ (palette q)) v ↔ q.val < 2
    rw [← mem_criticalColors, hhigh v, hσ q]
  refine ⟨σ, relabel_noMono c hc _ _, ?_, hn⟩
  intro v q
  by_cases hq : q.val < 2
  · simp only [if_pos hq, relabel_degree]
    exact fourColor_colorDegree_le_sixteen c hc _ _
  · have hlow : ¬15 ≤ colorDegree (relabel c (Equiv.refl _) σ) (palette q) v :=
      mt (hn v q).mp hq
    simp only [if_neg hq]
    omega

/-- The named generic caps permit all four possible deficiency colors. -/
theorem named_caps_vectors (c : Host) (hn : NamedCaps c) (v : Vertex) :
    (colorDegree c (palette 0) v = 15 ∧ colorDegree c (palette 1) v = 16 ∧
      colorDegree c (palette 2) v = 14 ∧ colorDegree c (palette 3) v = 14) ∨
    (colorDegree c (palette 0) v = 16 ∧ colorDegree c (palette 1) v = 15 ∧
      colorDegree c (palette 2) v = 14 ∧ colorDegree c (palette 3) v = 14) ∨
    (colorDegree c (palette 0) v = 16 ∧ colorDegree c (palette 1) v = 16 ∧
      colorDegree c (palette 2) v = 13 ∧ colorDegree c (palette 3) v = 14) ∨
    (colorDegree c (palette 0) v = 16 ∧ colorDegree c (palette 1) v = 16 ∧
      colorDegree c (palette 2) v = 14 ∧ colorDegree c (palette 3) v = 13) := by
  apply named_degree_vectors
  · simpa using hn v 0
  · simpa using hn v 1
  · simpa using hn v 2
  · simpa using hn v 3
  · simpa [palette] using fourColor_degree_sum c v

/-- C1 uses16/16/13/14; C2 uses15/16/14/14. -/
def firstSize (c1 : Bool) : Nat := if c1 then 16 else 15

def canonicalDegree (c1 : Bool) (q : Color) : Nat :=
  if q.val = 0 then firstSize c1 else if q.val = 1 then 16
  else if q.val = 2 then 29 - firstSize c1 else 14

def canonicalCell (c1 : Bool) (v : Vertex) : Option FourColor :=
  if v = 0 then none else if v.val ≤ firstSize c1 then some (palette 0)
  else if v.val ≤ firstSize c1 + 16 then some (palette 1)
  else if v.val ≤ 45 then some (palette 2) else some (palette 3)

set_option maxRecDepth 10000 in
theorem canonicalCell_none : ∀ c1 v, canonicalCell c1 v = none ↔ v = 0 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem canonicalCell_card : ∀ c1 q,
    Fintype.card {v // canonicalCell c1 v = some (palette q)} = canonicalDegree c1 q := by
  decide

/-- Both balanced root partitions are normalized by the same finite-fiber theorem. -/
theorem exists_balanced_root_equiv (c : Host) (r : Vertex)
    (σ : Equiv.Perm FourColor) (c1 : Bool)
    (hd : ∀ q : Color, colorDegree c (σ (palette q)) r = canonicalDegree c1 q) :
    ∃ e : Vertex ≃ Vertex, e 0 = r ∧
      ∀ v, rootCell c r σ (e v) = canonicalCell c1 v := by
  apply exists_root_cell_equiv c r σ (canonicalCell c1) (canonicalCell_none c1)
  intro q
  obtain ⟨q, rfl⟩ := palette_surjective q
  rw [canonicalCell_card, hd]

#print axioms common_pair_to_named
#print axioms named_caps_vectors
#print axioms exists_balanced_root_equiv
end UniformK60.HostNormalization
