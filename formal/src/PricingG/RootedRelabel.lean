import PricingG.SixStarCanonical

namespace PricingG.SignDesign
open Finset PricingC

theorem inducedDegreeTwo_image {K L : SimpleGraph (Fin 16)}
    [DecidableRel K.Adj] [DecidableRel L.Adj] (e : K ≃g L) (A : Finset (Fin 16))
    (hA : InducedDegreeTwo K A) : InducedDegreeTwo L (A.image e) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  rw [graphIso_filter_card]
  exact hA a ha

theorem rootedPentagonLaw_image {K L : SimpleGraph (Fin 16)}
    [DecidableRel K.Adj] [DecidableRel L.Adj] (e : K ≃g L) (v : Fin 16) (A : Finset (Fin 16))
    (hA : RootPentagonLaw K v A) : RootPentagonLaw L (e v) (A.image e) := by
  intro x
  obtain ⟨a,rfl⟩ := e.surjective x
  rw [graphIso_filter_card,hA a]
  simp [e.injective.eq_iff,e.map_rel_iff,mem_image]

noncomputable def conjugatedImage (e : xorGraph ≃g xorGraph) (ρ : Equiv.Perm (Fin 16)) :=
  e.toEquiv.trans (ρ.trans e.toEquiv.symm)

/-- One simultaneous relabeling of the shared graph changes the image rule
by conjugation; separate row relabelings are not permitted here. -/
theorem rootedDichotomy_relabel (σ σ' ρ : Equiv.Perm (Fin 16))
    (e : xorGraph ≃g xorGraph)
    (eJ : permutedGraph σ' ≃g permutedGraph σ) (he : eJ.toEquiv = e.toEquiv)
    (hd : RootedDichotomy σ ρ) : RootedDichotomy σ' (conjugatedImage e ρ) := by
  intro y
  have himage : ((permutedGraph σ').neighborFinset y).image e =
      (permutedGraph σ).neighborFinset (e y) := by
    have h := graphIso_neighbor_image eJ y
    change ((permutedGraph σ').neighborFinset y).image eJ.toEquiv =
      (permutedGraph σ).neighborFinset (eJ.toEquiv y) at h
    rw [he] at h
    exact h
  have hpull : ((permutedGraph σ).neighborFinset (e y)).image e.symm =
      (permutedGraph σ').neighborFinset y := by
    rw [← himage,Finset.image_image]
    simp
  rcases hd (e y) with hs | hp
  · obtain ⟨a,hpa,ha⟩ := hs
    left
    refine ⟨e.symm a,?_,?_⟩
    · exact e.symm.map_rel_iff.mpr hpa
    · rw [← hpull,ha,graphIso_neighbor_image]
  · right
    constructor
    · rw [← hpull]
      exact inducedDegreeTwo_image e.symm _ hp.1
    · change RootPentagonLaw xorGraph (e.symm (ρ (e y))) _
      rw [← hpull]
      exact rootedPentagonLaw_image e.symm _ _ hp.2

theorem starCount_relabel (σ σ' : Equiv.Perm (Fin 16))
    (e : xorGraph ≃g xorGraph)
    (eJ : permutedGraph σ' ≃g permutedGraph σ) (he : eJ.toEquiv = e.toEquiv) :
    (starSet σ').card = (starSet σ).card := by
  have hdeg (y : Fin 16) : InducedDegreeTwo xorGraph ((permutedGraph σ').neighborFinset y) ↔
      InducedDegreeTwo xorGraph ((permutedGraph σ).neighborFinset (e y)) := by
    have himage : ((permutedGraph σ').neighborFinset y).image e =
      (permutedGraph σ).neighborFinset (e y) := by
      have h := graphIso_neighbor_image eJ y
      change ((permutedGraph σ').neighborFinset y).image eJ.toEquiv =
        (permutedGraph σ).neighborFinset (eJ.toEquiv y) at h
      rw [he] at h
      exact h
    constructor
    · intro h
      rw [← himage]
      exact inducedDegreeTwo_image e _ h
    · intro h
      have hp := inducedDegreeTwo_image e.symm _ h
      rw [← himage,Finset.image_image] at hp
      simpa using hp
  have heq : (starSet σ').image e = starSet σ := by
    ext x
    constructor
    · intro h
      obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      simp only [starSet,mem_filter,mem_univ,true_and] at hy ⊢
      exact fun hp => hy ((hdeg y).mpr hp)
    · intro h
      refine mem_image.mpr ⟨e.symm x,?_,e.apply_symm_apply x⟩
      simp only [starSet,mem_filter,mem_univ,true_and] at h ⊢
      intro hp
      have hh := (hdeg (e.symm x)).mp hp
      have hx : e (e.symm x) = x := e.apply_symm_apply x
      exact h (hx ▸ hh)
  have hc := congrArg Finset.card heq
  rwa [card_image_of_injective _ e.injective] at hc

def shiftFn (v : Fin 16) (u : Fin 16) := R4333.xorIndex16 v u
private theorem shift_inverse : ∀ v, Function.LeftInverse (shiftFn v) (shiftFn v) := by decide

def shift (v : Fin 16) : Equiv.Perm (Fin 16) where
  toFun := shiftFn v
  invFun := shiftFn v
  left_inv := shift_inverse v
  right_inv := shift_inverse v

def shiftIso (v : Fin 16) : xorGraph ≃g xorGraph where
  toEquiv := shift v
  map_rel_iff' := by revert v; decide

@[simp] theorem shift_zero : ∀ v, shift v 0 = v := by decide
@[simp] theorem shift_self : ∀ v, shift v v = 0 := by decide

noncomputable def rerootPermutation (σ : Equiv.Perm (Fin 16)) (v : Fin 16) : Equiv.Perm (Fin 16) :=
  (shift v).trans (σ.trans (shift (σ v)))

def rerootGraphIso (σ : Equiv.Perm (Fin 16)) (v : Fin 16) :
    permutedGraph (rerootPermutation σ v) ≃g permutedGraph σ where
  toEquiv := shift v
  map_rel_iff' := by
    intro a b
    change xorGraph.Adj (σ (shift v a)) (σ (shift v b)) ↔
      xorGraph.Adj (shift (σ v) (σ (shift v a))) (shift (σ v) (σ (shift v b)))
    exact (shiftIso (σ v)).map_rel_iff.symm

@[simp] theorem reroot_zero (σ : Equiv.Perm (Fin 16)) (v : Fin 16) :
    rerootPermutation σ v 0 = 0 := by simp [rerootPermutation]

/-- Exclusion of ten pentagonal neighborhoods on every common labeling. -/
theorem no_six_star_rows (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).card = 6) : False := by
  obtain ⟨v,hv,hcommon⟩ := six_stars_have_common_center σ ρ hd hs
  let σ' := rerootPermutation σ v
  let e := shiftIso v
  let ρ' := conjugatedImage e ρ
  have hd' : RootedDichotomy σ' ρ' :=
    rootedDichotomy_relabel σ σ' ρ e (rerootGraphIso σ v) rfl hd
  have hs' : (starSet σ').card = 6 := by
    rw [starCount_relabel σ σ' e (rerootGraphIso σ v) rfl,hs]
  have hroot : (permutedGraph σ').neighborFinset 0 = xorGraph.neighborFinset 0 := by
    apply Finset.image_injective e.injective
    have hJ := graphIso_neighbor_image (rerootGraphIso σ v) 0
    have hK := graphIso_neighbor_image e 0
    change ((permutedGraph σ').neighborFinset 0).image e = _ at hJ
    rw [hJ,hK]
    change (permutedGraph σ).neighborFinset (shift v 0) = xorGraph.neighborFinset (shift v 0)
    rw [shift_zero]
    exact hcommon
  exact no_six_stars_canonical σ' ρ' hd' hs' (reroot_zero σ v) hroot

#print axioms no_six_star_rows
end PricingG.SignDesign
