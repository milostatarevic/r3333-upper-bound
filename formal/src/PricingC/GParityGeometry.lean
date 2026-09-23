import PricingG.StarPentagonTransport

namespace PricingC.GParity
open Finset PricingC PricingG

 def oddSupport (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (A : Finset (Fin 16)) : Finset (Fin 16) :=
  univ.filter fun x => Odd ((A.filter fun a => K.Adj x a).card)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
 theorem canonical_pentagon_odd_support : ∀ A : fiveCandidates,
    InducedDegreeTwo xorGraph A.val → RootMaskCondition xorGraph 0 A.val →
    (oddSupport xorGraph A.val).card = 5 ∧ InducedDegreeTwo xorGraph (oddSupport xorGraph A.val) := by decide

 theorem oddSupport_image {K L : SimpleGraph (Fin 16)}
    [DecidableRel K.Adj] [DecidableRel L.Adj] (e : K ≃g L) (A : Finset (Fin 16)) :
    (oddSupport K A).image e = oddSupport L (A.image e) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    have hh := (mem_filter.mp hx).2
    apply mem_filter.mpr
    exact ⟨mem_univ _,by rwa [graphIso_filter_card]⟩
  · intro hy
    refine mem_image.mpr ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have hh := (mem_filter.mp hy).2
    have he := graphIso_filter_card e A (e.symm y)
    rw [e.apply_symm_apply] at he
    rwa [he] at hh

/-- The odd-incidence support of an actual rooted pentagon is another
physical five-set inducing a pentagon in the same K graph. -/
 theorem pentagon_odd_support (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (v : Fin 16) (A : Finset (Fin 16))
    (hA : A.card = 5) (hcycle : InducedDegreeTwo K A) (hlaw : RootPentagonLaw K v A) :
    (oddSupport K A).card = 5 ∧ InducedDegreeTwo K (oddSupport K A) := by
  classical
  have havoid : Disjoint A (K.neighborFinset v) := by
    apply disjoint_left.mpr
    intro x hx hn
    have hz := hlaw v
    simp only [if_pos rfl] at hz
    have hm : x ∈ A.filter (fun a => K.Adj v a) :=
      mem_filter.mpr ⟨hx,(K.mem_neighborFinset _ _).mp hn⟩
    rw [card_eq_zero.mp hz] at hm
    simp at hm
  have hmask : RootMaskCondition K v A := by
    intro x hx
    left
    have h := hlaw x
    have hxv : x ≠ v := by intro he; subst x; exact K.loopless.irrefl v ((K.mem_neighborFinset _ _).mp hx)
    simpa only [hxv,if_false,(K.mem_neighborFinset _ _).mp hx,or_true,if_true] using h
  have hpoints : Fintype.card ↥(R4333.clebschA K v) = 5 := by
    simpa only [Fintype.card_coe] using R4333.card_clebschA K hK v
  let points : Fin 5 ≃ ↥(R4333.clebschA K v) := (Fintype.equivFinOfCardEq hpoints).symm
  let e := anchoredCoordinates K hK v points
  have he0 : e 0 = v := anchoredCoordinates_root K hK v points
  let A' := A.image e.symm
  have heA : A'.image e = A := by simp [A',Finset.image_image]
  have hcA : A'.card = 5 := by rw [card_image_of_injective _ e.symm.injective]; exact hA
  have hsub : A' ⊆ univ \ xorGraph.neighborFinset 0 := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hn
    have hg := e.map_rel_iff.mpr ((xorGraph.mem_neighborFinset _ _).mp hn)
    rw [he0,e.apply_symm_apply] at hg
    exact disjoint_left.mp havoid ha ((K.mem_neighborFinset _ _).mpr hg)
  have hmask' : RootMaskCondition xorGraph 0 A' := by
    intro x hx
    have hex : e x ∈ K.neighborFinset v := by
      apply (K.mem_neighborFinset _ _).mpr
      rw [←he0]
      exact e.map_rel_iff.mpr ((xorGraph.mem_neighborFinset _ _).mp hx)
    have hm := hmask (e x) hex
    have he := graphIso_filter_card e A' x
    rw [heA] at he
    rwa [he] at hm
  have hcycle' : InducedDegreeTwo xorGraph A' := by
    intro x hx
    have hxA : e x ∈ A := by rw [←heA]; exact mem_image.mpr ⟨x,hx,rfl⟩
    have hm := hcycle (e x) hxA
    have he := graphIso_filter_card e A' x
    rw [heA] at he
    rwa [he] at hm
  obtain ⟨hsize,hpent⟩ := canonical_pentagon_odd_support
    ⟨A',mem_powersetCard.mpr ⟨hsub,hcA⟩⟩ hcycle' hmask'
  have ho : (oddSupport xorGraph A').image e = oddSupport K A := by
    rw [oddSupport_image,heA]
  refine ⟨?_,?_⟩
  · rw [←ho,card_image_of_injective _ e.injective]
    exact hsize
  · intro x hx
    obtain ⟨x',hx',rfl⟩ := mem_image.mp (ho.symm ▸ hx)
    have hh := hpent x' hx'
    have he := graphIso_filter_card e (oddSupport xorGraph A') x'
    rw [ho] at he
    rwa [he]

#print axioms pentagon_odd_support
end PricingC.GParity
