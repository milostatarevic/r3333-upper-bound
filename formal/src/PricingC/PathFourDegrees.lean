import PricingC.DegreeFourPathPhysical

namespace PricingC.DegreeFourPath
open Finset

/-- Coordinate-free row-degree form of the exactP4 predicate used by all
U/T support orbit catalogues. -/
theorem path_four_degrees {n:Nat} (d:Fin n→Fin n→Fin 3) (s:Finset (Fin n))
 (e:Fin 4↪Fin n) (hs:univ.image e=s)
 (hpath:∀i j:Fin 4,i≠j → (d (e i) (e j)=0 ↔ PathAdjacent i j)):
 (∀a∈s,(s.filter fun b=>b≠a ∧ d a b=0).card=1 ∨ (s.filter fun b=>b≠a ∧ d a b=0).card=2) ∧
 (s.filter fun a=>(s.filter fun b=>b≠a ∧ d a b=0).card=1).card=2:=by
 have hpne:∀i j:Fin 4,PathAdjacent i j → i≠j:=by decide
 have row_eq (i:Fin 4):s.filter (fun b=>b≠e i ∧ d (e i) b=0)=
  (univ.filter fun j:Fin 4=>PathAdjacent i j).image e:=by
  ext v
  constructor
  · intro hv
    obtain ⟨hv,hvi,hcol⟩:=mem_filter.mp hv
    rw[←hs] at hv
    obtain ⟨j,_,rfl⟩:=mem_image.mp hv
    apply mem_image.mpr
    refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
    exact (hpath i j (by intro hh;subst j;exact hvi rfl)).mp hcol
  · intro hv
    obtain ⟨j,hj,rfl⟩:=mem_image.mp hv
    have hp:=(mem_filter.mp hj).2
    apply mem_filter.mpr
    refine ⟨?_,e.injective.ne (hpne i j hp).symm,(hpath i j (hpne i j hp)).mpr hp⟩
    rw[←hs]
    exact mem_image.mpr ⟨j,mem_univ _,rfl⟩
 have row_card (i:Fin 4):(s.filter fun b=>b≠e i ∧ d (e i) b=0).card=
  (univ.filter fun j:Fin 4=>PathAdjacent i j).card:=by
  rw[row_eq,card_image_of_injective _ e.injective]
 have hdegree:∀i:Fin 4,(univ.filter fun j:Fin 4=>PathAdjacent i j).card=1 ∨
  (univ.filter fun j:Fin 4=>PathAdjacent i j).card=2:=by decide
 refine ⟨?_,?_⟩
 · intro a ha
   rw[←hs] at ha
   obtain ⟨i,_,rfl⟩:=mem_image.mp ha
   rw[row_card]
   exact hdegree i
 · have he:s.filter (fun a=>(s.filter fun b=>b≠a ∧ d a b=0).card=1)=
    (univ.filter fun i:Fin 4=>(univ.filter fun j:Fin 4=>PathAdjacent i j).card=1).image e:=by
    ext v
    constructor
    · intro hv
      obtain ⟨hv,hvdeg⟩:=mem_filter.mp hv
      rw[←hs] at hv
      obtain ⟨i,_,rfl⟩:=mem_image.mp hv
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,(row_card i).symm.trans hvdeg⟩,rfl⟩
    · intro hv
      obtain ⟨i,hi,rfl⟩:=mem_image.mp hv
      apply mem_filter.mpr
      refine ⟨?_,(row_card i).trans (mem_filter.mp hi).2⟩
      rw[←hs]
      exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
   rw[he,card_image_of_injective _ e.injective]
   decide

#print axioms path_four_degrees
end PricingC.DegreeFourPath
