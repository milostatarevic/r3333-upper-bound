import R4333Lean.SingleRootStarWitness61

/-!
# Global own-block-colour degree accounting in a canonical K61 star

The sixty non-root vertices still form a triangle-free four-colouring.
Consequently every displayed colour degree is at most sixteen.  Since the
four degrees at a non-root vertex sum to fifty-nine, its root-block colour
occurs on at least eleven non-root edges.  Summed over all sixty vertices,
this gives the exact global lower bound 660 used when judging local pair
cuts.
-/

namespace R4333
namespace CanonicalStarOwnColorDegree

open SingleRootStarCNF
open SingleRootStarWitness61

/-- The root-neighbourhood block containing a canonical non-root vertex. -/
noncomputable def vertexBlock (profile : Profile) (x : Fin 60) : Fin 4 :=
  (blockPositionEquiv profile x).1

/-- Every colour degree in the non-root K60 is at most sixteen. -/
theorem witness_colorDegree_le_sixteen {profile : Profile}
    (w : CanonicalStarWitness profile) (q : Fin 4) (x : Fin 60) :
    colorDegree w.coloring q x ≤ 16 := by
  fin_cases q
  · exact colorDegree_le_sixteen_of_four w.coloring w.noMono
      0 1 2 3 (by intro z; fin_cases z <;> simp) x
  · exact colorDegree_le_sixteen_of_four w.coloring w.noMono
      1 0 2 3 (by intro z; fin_cases z <;> simp) x
  · exact colorDegree_le_sixteen_of_four w.coloring w.noMono
      2 0 1 3 (by intro z; fin_cases z <;> simp) x
  · exact colorDegree_le_sixteen_of_four w.coloring w.noMono
      3 0 1 2 (by intro z; fin_cases z <;> simp) x

/-- In fact every one of the four non-root colour degrees is at least
eleven; the own-block instance is the form used below. -/
theorem witness_colorDegree_ge_eleven {profile : Profile}
    (w : CanonicalStarWitness profile) (q : Fin 4) (x : Fin 60) :
    11 ≤ colorDegree w.coloring q x := by
  have hsum := sum_colorDegree_eq_card_sub_one w.coloring x
  have h0 := witness_colorDegree_le_sixteen w 0 x
  have h1 := witness_colorDegree_le_sixteen w 1 x
  have h2 := witness_colorDegree_le_sixteen w 2 x
  have h3 := witness_colorDegree_le_sixteen w 3 x
  have hsum' :
      colorDegree w.coloring 0 x +
        (colorDegree w.coloring 1 x +
          (colorDegree w.coloring 2 x + colorDegree w.coloring 3 x)) = 59 := by
    simpa [Fin.sum_univ_succ] using hsum
  fin_cases q
  · change 11 ≤ colorDegree w.coloring 0 x
    omega
  · change 11 ≤ colorDegree w.coloring 1 x
    omega
  · change 11 ≤ colorDegree w.coloring 2 x
    omega
  · change 11 ≤ colorDegree w.coloring 3 x
    omega

/-- Each non-root vertex has at least eleven incident non-root edges in its
own root-block colour. -/
theorem ownBlockColorDegree_ge_eleven {profile : Profile}
    (w : CanonicalStarWitness profile) (x : Fin 60) :
    11 ≤ colorDegree w.coloring (vertexBlock profile x) x :=
  witness_colorDegree_ge_eleven w (vertexBlock profile x) x

/-- Global endpoint-incidence lower bound: the sum of the sixty own-block
colour degrees is at least `60 * 11 = 660`. -/
theorem totalOwnBlockColorDegree_ge_sixHundredSixty {profile : Profile}
    (w : CanonicalStarWitness profile) :
    660 ≤ ∑ x : Fin 60,
      colorDegree w.coloring (vertexBlock profile x) x := by
  calc
    660 = ∑ _x : Fin 60, 11 := by simp
    _ ≤ ∑ x : Fin 60,
        colorDegree w.coloring (vertexBlock profile x) x :=
      Finset.sum_le_sum fun x _ => ownBlockColorDegree_ge_eleven w x

#print axioms R4333.CanonicalStarOwnColorDegree.totalOwnBlockColorDegree_ge_sixHundredSixty

end CanonicalStarOwnColorDegree
end R4333
