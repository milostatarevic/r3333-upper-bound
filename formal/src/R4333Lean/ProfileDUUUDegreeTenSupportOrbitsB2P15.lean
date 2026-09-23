import R4333Lean.ProfileDUUUDegreeTenSupportOrbits61

/-!
# Color-two K15 support orbits for UUU / block two / position fifteen

When the selected endpoint lies in block two, its own color is three.  In
both foreign untwisted K15 blocks that color is template label two.  This
module enumerates all eleven independent five-sets and gives explicit strong
template automorphisms reducing them to representatives `0`, `1`, and `4`.

The normalizers are compositions of already checked strong automorphisms.
Every finite table statement is checked by ordinary kernel reduction.
-/

namespace R4333
namespace ProfileDUUUDegreeTenSupportOrbitsB2P15

open CriticalK15PartitionClassification
open ProfileDUUUDegreeTenSupportOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def q2Support : Fin 11 → Finset (Fin 15) :=
  ![{0, 1, 2, 10, 13},
    {0, 1, 3, 11, 12},
    {0, 7, 8, 10, 11},
    {1, 2, 3, 9, 14},
    {1, 6, 9, 10, 11},
    {1, 6, 12, 13, 14},
    {2, 5, 8, 9, 10},
    {3, 4, 8, 9, 11},
    {4, 5, 6, 9, 14},
    {4, 6, 7, 11, 12},
    {5, 6, 7, 10, 13}]

def q2SupportFamily : Finset (Finset (Fin 15)) :=
  Finset.univ.image q2Support

theorem q2SupportFamily_complete :
    independentFiveSets false 2 = q2SupportFamily := by
  decide

theorem q2SupportFamily_card : q2SupportFamily.card = 11 := by
  decide

theorem q2Support_card (i : Fin 11) : (q2Support i).card = 5 := by
  fin_cases i <;> decide

theorem q2Support_independent (i : Fin 11) :
    IsColorIndependentSet (k15Template false) 2 (q2Support i) := by
  apply (colorViolationCount_eq_zero_iff _ _ _).mp
  fin_cases i <;> decide

/-! ## Explicit strong normalizers -/

def q2SupportRepresentative : Fin 11 → Fin 11 :=
  ![0, 1, 1, 1, 4, 0, 0, 0, 1, 0, 1]

def q2FirstActionIndex : Fin 11 → Fin 11 :=
  ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 3]

def q2SecondActionIndex : Fin 11 → Fin 11 :=
  ![0, 0, 1, 3, 0, 8, 3, 5, 3, 4, 1]

def q2SupportMap (i : Fin 11) (vertex : Fin 15) : Fin 15 :=
  u15SupportMap (q2SecondActionIndex i)
    (u15SupportMap (q2FirstActionIndex i) vertex)

theorem q2SupportRepresentative_mem (i : Fin 11) :
    q2SupportRepresentative i ∈ ({0, 1, 4} : Finset (Fin 11)) := by
  fin_cases i <;> decide

theorem q2SupportMap_bijective (i : Fin 11) :
    Function.Bijective (q2SupportMap i) := by
  unfold q2SupportMap
  exact (u15SupportMap_bijective (q2SecondActionIndex i)).comp
    (u15SupportMap_bijective (q2FirstActionIndex i))

theorem q2SupportMap_preserves (i : Fin 11)
    (left right : Fin 15) (hne : left ≠ right) :
    k15Template false (q2SupportMap i left) (q2SupportMap i right) =
      k15Template false left right := by
  have hinner :
      u15SupportMap (q2FirstActionIndex i) left ≠
        u15SupportMap (q2FirstActionIndex i) right :=
    (u15SupportMap_bijective (q2FirstActionIndex i)).1.ne hne
  calc
    k15Template false (q2SupportMap i left) (q2SupportMap i right) =
        k15Template false
          (u15SupportMap (q2FirstActionIndex i) left)
          (u15SupportMap (q2FirstActionIndex i) right) :=
      u15SupportMap_preserves (q2SecondActionIndex i) _ _ hinner
    _ = k15Template false left right :=
      u15SupportMap_preserves (q2FirstActionIndex i) left right hne

theorem q2SupportMap_image (i : Fin 11) :
    (q2Support i).image (q2SupportMap i) =
      q2Support (q2SupportRepresentative i) := by
  fin_cases i <;> decide

noncomputable def q2SupportEquiv (i : Fin 11) : Equiv.Perm (Fin 15) :=
  Equiv.ofBijective (q2SupportMap i) (q2SupportMap_bijective i)

@[simp] theorem q2SupportEquiv_apply (i : Fin 11) (vertex : Fin 15) :
    q2SupportEquiv i vertex = q2SupportMap i vertex := rfl

noncomputable def q2StrongNormalizer (i : Fin 11) :
    StrongTemplateAutomorphism 15 (k15Template false) where
  vertex := q2SupportEquiv i
  preserves := by
    intro left right hne
    exact q2SupportMap_preserves i left right hne

theorem exists_q2_strong_support_normalization (i : Fin 11) :
    ∃ representative ∈ ({0, 1, 4} : Finset (Fin 11)),
      ∃ e : StrongTemplateAutomorphism 15 (k15Template false),
        (q2Support i).image e.vertex = q2Support representative := by
  refine ⟨q2SupportRepresentative i, q2SupportRepresentative_mem i,
    q2StrongNormalizer i, ?_⟩
  change (q2Support i).image (q2SupportMap i) =
    q2Support (q2SupportRepresentative i)
  exact q2SupportMap_image i

theorem exists_q2_strong_support_pair_normalization (first second : Fin 11) :
    ∃ firstRepresentative ∈ ({0, 1, 4} : Finset (Fin 11)),
      ∃ secondRepresentative ∈ ({0, 1, 4} : Finset (Fin 11)),
        ∃ firstEquiv secondEquiv :
            StrongTemplateAutomorphism 15 (k15Template false),
          (q2Support first).image firstEquiv.vertex =
              q2Support firstRepresentative ∧
            (q2Support second).image secondEquiv.vertex =
              q2Support secondRepresentative := by
  obtain ⟨firstRepresentative, hfirstRepresentative, firstEquiv, hfirst⟩ :=
    exists_q2_strong_support_normalization first
  obtain ⟨secondRepresentative, hsecondRepresentative, secondEquiv, hsecond⟩ :=
    exists_q2_strong_support_normalization second
  exact ⟨firstRepresentative, hfirstRepresentative,
    secondRepresentative, hsecondRepresentative,
    firstEquiv, secondEquiv, hfirst, hsecond⟩

#print axioms q2SupportFamily_complete
#print axioms q2SupportMap_preserves
#print axioms exists_q2_strong_support_normalization
#print axioms exists_q2_strong_support_pair_normalization

end ProfileDUUUDegreeTenSupportOrbitsB2P15
end R4333
