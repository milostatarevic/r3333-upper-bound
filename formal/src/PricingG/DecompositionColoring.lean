import PricingG.ComplementDecomposition

namespace PricingG
open Finset Matrix

theorem triangle_impossible_of_square_zero (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (hs : ∀ x y, G.Adj x y → (G.adjMatrix ℤ * G.adjMatrix ℤ) x y = 0)
    (x y z : Fin 16) (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : False := by
  have hz := (G.mem_neighborFinset y z).mpr hyz
  have hn (v : Fin 16) (_ : v ∈ G.neighborFinset y) : (0 : ℤ) ≤ G.adjMatrix ℤ x v := by
    simp only [SimpleGraph.adjMatrix_apply]; positivity
  have hle := single_le_sum hn hz
  have hs' := hs x y hxy
  rw [G.mul_adjMatrix_apply] at hs'
  rw [hs',SimpleGraph.adjMatrix_apply,if_pos hxz] at hle
  omega

theorem third_triangle_impossible (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) (x y z : Fin 16)
    (hxy : (thirdGraph K J).Adj x y) (hxz : (thirdGraph K J).Adj x z)
    (hyz : (thirdGraph K J).Adj y z) : False := by
  apply triangle_impossible_of_square_zero (thirdGraph K J) _ x y z hxy hxz hyz
  intro a b hab
  rw [full_defects_third_square K J hK hJ ρ hd hz]
  have hab' : a ≠ b ∧ ¬(K.Adj a b ∨ J.Adj a b) := hab
  change (5 : ℤ) * (if a = b then 1 else 0) +
    2 * (if K.Adj a b then 1 else 0) + 2 * (if J.Adj a b then 1 else 0) = 0
  simp only [if_neg hab'.1,if_neg (show ¬K.Adj a b from fun h => hab'.2 (Or.inl h)),
    if_neg (show ¬J.Adj a b from fun h => hab'.2 (Or.inr h)),mul_zero,add_zero]

def decompositionColoring (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] : R4333.EdgeColoring (Fin 16) (Fin 3) where
  color x y := if K.Adj x y then 0 else if J.Adj x y then 1 else 2
  color_symm x y := by simp only [K.adj_comm x y,J.adj_comm x y]

theorem decomposition_zero_iff (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (x y : Fin 16) :
    decompositionColoring K J x y = 0 ↔ K.Adj x y := by
  change (if K.Adj x y then (0 : Fin 3) else if J.Adj x y then 1 else 2) = 0 ↔ _
  split_ifs <;> simp_all

theorem decomposition_one_iff (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (hd : ∀ x y, ¬(K.Adj x y ∧ J.Adj x y)) (x y : Fin 16) :
    decompositionColoring K J x y = 1 ↔ J.Adj x y := by
  have hdis := hd x y
  change (if K.Adj x y then (0 : Fin 3) else if J.Adj x y then 1 else 2) = 1 ↔ _
  split_ifs <;> simp_all

theorem decomposition_two_iff (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (x y : Fin 16) (hxy : x ≠ y) :
    decompositionColoring K J x y = 2 ↔ (thirdGraph K J).Adj x y := by
  change (if K.Adj x y then (0 : Fin 3) else if J.Adj x y then 1 else 2) = 2 ↔
    x ≠ y ∧ ¬(K.Adj x y ∨ J.Adj x y)
  split_ifs <;> simp_all

/-- The full-defect endpoint supplies a genuine triangle-free three-color
completion. Its third color is proved valid, not assumed from the table. -/
theorem full_defects_good_coloring (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) : R4333.NoMonochromaticTriangle (decompositionColoring K J) := by
  intro x y z hdist hmono
  obtain ⟨hxy,hxz,hyz⟩ := hdist
  obtain ⟨h1,h2⟩ := hmono
  have hdis := full_defects_disjoint K J hK hJ hd.unrooted hz
  generalize he : decompositionColoring K J x y = a
  have hexz : decompositionColoring K J x z = a := h1.symm.trans he
  have heyz : decompositionColoring K J y z = a := h2.symm.trans hexz
  fin_cases a
  · have e1 := (decomposition_zero_iff K J x y).mp he
    have e2 := (decomposition_zero_iff K J x z).mp hexz
    have e3 := (decomposition_zero_iff K J y z).mp heyz
    exact R4333.clebschA_pair_not_adj K hK
      ((K.mem_neighborFinset x y).mpr e1) ((K.mem_neighborFinset x z).mpr e2) e3
  · have e1 := (decomposition_one_iff K J hdis x y).mp he
    have e2 := (decomposition_one_iff K J hdis x z).mp hexz
    have e3 := (decomposition_one_iff K J hdis y z).mp heyz
    exact R4333.clebschA_pair_not_adj J hJ
      ((J.mem_neighborFinset x y).mpr e1) ((J.mem_neighborFinset x z).mpr e2) e3
  · exact third_triangle_impossible K J hK hJ ρ hd hz x y z
      ((decomposition_two_iff K J x y hxy).mp he)
      ((decomposition_two_iff K J x z hxz).mp hexz)
      ((decomposition_two_iff K J y z hyz).mp heyz)

/-- All full-defect shared graph decompositions are in the exact retained
72-row table after one common vertex relabeling and the fixed 0/1/2 palette. -/
theorem full_defects_exact72_coordinates (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) (e : PricingC.xorGraph ≃g K) :
    ∃ (i : Fin 72), ∀ u v, u ≠ v →
      decompositionColoring K J (e u) (e v) = Completion72.referenceColor i u v := by
  let d := R4333.relabelVertices (decompositionColoring K J) e.toEquiv
  have hgood : R4333.NoMonochromaticTriangle d :=
    R4333.noMono_relabelVertices _ _ (full_defects_good_coloring K J hK hJ ρ hd hz)
  have hzero : ∀ u v, u ≠ v → (d u v = 0 ↔ Completion72.xorClebsch u v = true) := by
    intro u v huv
    change decompositionColoring K J (e u) (e v) = 0 ↔ _
    rw [decomposition_zero_iff,e.map_rel_iff]
    exact (show ∀ u v, PricingC.xorGraph.Adj u v ↔ Completion72.xorClebsch u v = true from by decide) u v
  obtain ⟨i,hi⟩ := Completion72.reference_exhaustive d hgood hzero
  exact ⟨i,hi⟩

theorem full_defects_exact72 (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) :
    ∃ (e : PricingC.xorGraph ≃g K) (i : Fin 72), ∀ u v, u ≠ v →
      decompositionColoring K J (e u) (e v) = Completion72.referenceColor i u v := by
  obtain ⟨i,hi⟩ := full_defects_exact72_coordinates K J hK hJ ρ hd hz (coordinates K hK)
  exact ⟨coordinates K hK,i,hi⟩

#print axioms full_defects_good_coloring
#print axioms full_defects_exact72
end PricingG
