import R4333Lean.CriticalK15PartitionClassification

/-!
# Fixed-position support orbits for the UUU degree-ten branch

In the untwisted profile-D tail, a degree-ten endpoint has a five-element
colour-one-independent support in each foreign critical block.  This file
enumerates those supports and gives explicit strong (colour-preserving)
template automorphisms taking them to the support positions used by the
catalogue quotient.

There are eleven supports in `U15`, with representatives `0`, `2`, and `7`,
and sixteen supports in `U16`, forming one orbit with representative `0`.
All tables and all finite claims are checked by ordinary kernel reduction.
-/

namespace R4333
namespace ProfileDUUUDegreeTenSupportOrbits61

open CriticalK15PartitionClassification

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## The complete support tables -/

def u15Support : Fin 11 → Finset (Fin 15) :=
  ![{0, 1, 4, 8, 14},
    {0, 4, 5, 10, 12},
    {0, 6, 8, 9, 12},
    {1, 4, 5, 11, 13},
    {1, 7, 8, 9, 13},
    {2, 3, 6, 10, 12},
    {2, 3, 7, 11, 13},
    {2, 4, 8, 12, 13},
    {2, 4, 10, 11, 14},
    {2, 6, 7, 8, 14},
    {3, 5, 9, 12, 13}]

def u16Support : Fin 16 → Finset (Fin 16) :=
  ![{0, 1, 4, 8, 14},
    {0, 1, 5, 9, 15},
    {0, 4, 5, 10, 12},
    {0, 6, 8, 9, 12},
    {0, 6, 10, 14, 15},
    {1, 4, 5, 11, 13},
    {1, 7, 8, 9, 13},
    {1, 7, 11, 14, 15},
    {2, 3, 6, 10, 12},
    {2, 3, 7, 11, 13},
    {2, 4, 8, 12, 13},
    {2, 4, 10, 11, 14},
    {2, 6, 7, 8, 14},
    {3, 5, 9, 12, 13},
    {3, 5, 10, 11, 15},
    {3, 6, 7, 9, 15}]

def u15SupportFamily : Finset (Finset (Fin 15)) :=
  Finset.univ.image u15Support

def u16SupportFamily : Finset (Finset (Fin 16)) :=
  Finset.univ.image u16Support

def u16IndependentFiveSets : Finset (Finset (Fin 16)) :=
  ((Finset.univ : Finset (Fin 16)).powersetCard 5).filter fun S =>
    colorViolationCount (k16Template false) 1 S = 0

theorem u15SupportFamily_complete :
    independentFiveSets false 1 = u15SupportFamily := by
  decide

theorem u16SupportFamily_complete :
    u16IndependentFiveSets = u16SupportFamily := by
  decide

theorem u15SupportFamily_card : u15SupportFamily.card = 11 := by
  decide

theorem u16SupportFamily_card : u16SupportFamily.card = 16 := by
  decide

theorem u15Support_card (i : Fin 11) : (u15Support i).card = 5 := by
  fin_cases i <;> decide

theorem u16Support_card (i : Fin 16) : (u16Support i).card = 5 := by
  fin_cases i <;> decide

theorem u15Support_independent (i : Fin 11) :
    IsColorIndependentSet (k15Template false) 1 (u15Support i) := by
  apply (colorViolationCount_eq_zero_iff _ _ _).mp
  fin_cases i <;> decide

theorem u16Support_independent (i : Fin 16) :
    IsColorIndependentSet (k16Template false) 1 (u16Support i) := by
  apply (colorViolationCount_eq_zero_iff _ _ _).mp
  fin_cases i <;> decide

/-! ## Explicit U15 normalizers -/

def u15SupportRepresentative : Fin 11 → Fin 11 :=
  ![0, 0, 2, 2, 2, 2, 0, 7, 2, 0, 0]

def u15SupportMap : Fin 11 → Fin 15 → Fin 15 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ![0, 10, 13, 7, 4, 14, 9, 3, 12, 6, 1, 11, 8, 2, 5],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ![5, 9, 2, 14, 12, 0, 11, 7, 13, 1, 10, 6, 4, 8, 3],
    ![3, 9, 4, 14, 13, 7, 10, 0, 12, 6, 11, 1, 2, 8, 5],
    ![3, 11, 8, 0, 13, 5, 6, 14, 2, 10, 9, 1, 12, 4, 7],
    ![3, 9, 4, 14, 13, 7, 10, 0, 12, 6, 11, 1, 2, 8, 5],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ![5, 10, 8, 7, 12, 3, 1, 14, 4, 11, 9, 6, 13, 2, 0],
    ![5, 10, 8, 7, 12, 3, 1, 14, 4, 11, 9, 6, 13, 2, 0],
    ![5, 9, 2, 14, 12, 0, 11, 7, 13, 1, 10, 6, 4, 8, 3]]

theorem u15SupportRepresentative_mem (i : Fin 11) :
    u15SupportRepresentative i ∈ ({0, 2, 7} : Finset (Fin 11)) := by
  fin_cases i <;> decide

theorem u15SupportMap_bijective (i : Fin 11) :
    Function.Bijective (u15SupportMap i) := by
  fin_cases i <;> decide

theorem u15SupportMap_preserves (i : Fin 11) (u v : Fin 15) (huv : u ≠ v) :
    k15Template false (u15SupportMap i u) (u15SupportMap i v) =
      k15Template false u v := by
  fin_cases i <;> fin_cases u <;> fin_cases v <;> simp_all <;> decide

theorem u15SupportMap_image (i : Fin 11) :
    (u15Support i).image (u15SupportMap i) =
      u15Support (u15SupportRepresentative i) := by
  fin_cases i <;> decide

noncomputable def u15SupportEquiv (i : Fin 11) : Equiv.Perm (Fin 15) :=
  Equiv.ofBijective (u15SupportMap i) (u15SupportMap_bijective i)

@[simp] theorem u15SupportEquiv_apply (i : Fin 11) (u : Fin 15) :
    u15SupportEquiv i u = u15SupportMap i u := rfl

/-! ## Explicit U16 normalizers -/

def u16SupportMap : Fin 16 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8],
    ![0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12],
    ![0, 12, 7, 11, 9, 5, 14, 2, 8, 4, 15, 3, 1, 13, 6, 10],
    ![0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8],
    ![5, 4, 6, 7, 0, 1, 3, 2, 10, 11, 9, 8, 15, 14, 12, 13],
    ![2, 8, 15, 5, 6, 12, 11, 1, 14, 4, 3, 9, 10, 0, 7, 13],
    ![2, 8, 5, 15, 12, 6, 11, 1, 13, 7, 10, 0, 3, 9, 4, 14],
    ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13],
    ![3, 2, 0, 1, 6, 7, 5, 4, 12, 13, 15, 14, 9, 8, 10, 11],
    ![2, 10, 1, 9, 4, 12, 7, 15, 14, 6, 13, 5, 8, 0, 11, 3],
    ![5, 9, 14, 2, 0, 12, 11, 7, 15, 3, 4, 8, 10, 6, 1, 13],
    ![5, 10, 8, 7, 12, 3, 1, 14, 4, 11, 9, 6, 13, 2, 0, 15],
    ![5, 9, 2, 14, 12, 0, 11, 7, 13, 1, 10, 6, 4, 8, 3, 15],
    ![2, 10, 9, 1, 12, 4, 7, 15, 3, 11, 8, 0, 13, 5, 6, 14],
    ![5, 10, 7, 8, 3, 12, 1, 14, 15, 0, 13, 2, 9, 6, 11, 4]]

theorem u16SupportMap_bijective (i : Fin 16) :
    Function.Bijective (u16SupportMap i) := by
  fin_cases i <;> decide

theorem u16SupportMap_preserves (i : Fin 16) (u v : Fin 16) (huv : u ≠ v) :
    k16Template false (u16SupportMap i u) (u16SupportMap i v) =
      k16Template false u v := by
  fin_cases i <;> fin_cases u <;> fin_cases v <;> simp_all <;> decide

theorem u16SupportMap_image (i : Fin 16) :
    (u16Support i).image (u16SupportMap i) = u16Support 0 := by
  fin_cases i <;> decide

noncomputable def u16SupportEquiv (i : Fin 16) : Equiv.Perm (Fin 16) :=
  Equiv.ofBijective (u16SupportMap i) (u16SupportMap_bijective i)

@[simp] theorem u16SupportEquiv_apply (i : Fin 16) (u : Fin 16) :
    u16SupportEquiv i u = u16SupportMap i u := rfl

/-! ## Strong automorphism packages -/

structure StrongTemplateAutomorphism (n : Nat)
    (template : EdgeColoring (Fin n) ThreeColor) where
  vertex : Equiv.Perm (Fin n)
  preserves : ∀ u v, u ≠ v →
    template (vertex u) (vertex v) = template u v

noncomputable def u15StrongNormalizer (i : Fin 11) :
    StrongTemplateAutomorphism 15 (k15Template false) where
  vertex := u15SupportEquiv i
  preserves := by
    intro u v huv
    simpa using u15SupportMap_preserves i u v huv

noncomputable def u16StrongNormalizer (i : Fin 16) :
    StrongTemplateAutomorphism 16 (k16Template false) where
  vertex := u16SupportEquiv i
  preserves := by
    intro u v huv
    simpa using u16SupportMap_preserves i u v huv

theorem exists_u15_strong_support_normalization (i : Fin 11) :
    ∃ representative ∈ ({0, 2, 7} : Finset (Fin 11)),
      ∃ e : StrongTemplateAutomorphism 15 (k15Template false),
        (u15Support i).image e.vertex = u15Support representative := by
  refine ⟨u15SupportRepresentative i, u15SupportRepresentative_mem i,
    u15StrongNormalizer i, ?_⟩
  change (u15Support i).image (u15SupportMap i) =
    u15Support (u15SupportRepresentative i)
  exact u15SupportMap_image i

theorem exists_u16_strong_support_normalization (i : Fin 16) :
    ∃ e : StrongTemplateAutomorphism 16 (k16Template false),
      (u16Support i).image e.vertex = u16Support 0 := by
  refine ⟨u16StrongNormalizer i, ?_⟩
  change (u16Support i).image (u16SupportMap i) = u16Support 0
  exact u16SupportMap_image i

#print axioms R4333.ProfileDUUUDegreeTenSupportOrbits61.u15SupportFamily_complete
#print axioms R4333.ProfileDUUUDegreeTenSupportOrbits61.u16SupportFamily_complete
#print axioms R4333.ProfileDUUUDegreeTenSupportOrbits61.exists_u15_strong_support_normalization
#print axioms R4333.ProfileDUUUDegreeTenSupportOrbits61.exists_u16_strong_support_normalization

end ProfileDUUUDegreeTenSupportOrbits61
end R4333
