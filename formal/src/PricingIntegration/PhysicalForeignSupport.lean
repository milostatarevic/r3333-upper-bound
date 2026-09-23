import PricingIntegration.ABActualOwners
import PricingC.PathFourDegrees

set_option autoImplicit false
namespace PricingIntegration.PhysicalForeignSupport
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingIntegration.BActualFrame PricingC.DegreeFourPath

def owner (side : Bool) : Color := (localColor side).castSucc
private theorem owner_ne_three (side : Bool) : palette (owner side)≠palette 3 := by cases side <;> decide
private theorem foreign_zero_iff (side : Bool) (a : Fin 3) :
    (foreignEquiv (owner side) a).val=palette 0 ↔ a=0 := by cases side <;> fin_cases a <;> decide
private theorem foreign_two (side : Bool) : (foreignEquiv (owner side) 2).val=palette 3 := by cases side <;> rfl

def support {n : Nat} {c : Host} {r : Vertex} {side : Bool}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) t) (mark : Vertex) : Finset (Fin n) :=
    univ.filter fun i=>c mark (m.vertex i)=palette 3

theorem vertex_ne_mark {n : Nat} {c : Host} {r mark : Vertex} {side : Bool}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) t)
    (hm : mark∈colorNeighborhood c (palette 3) r) (i : Fin n) : m.vertex i≠mark := by
  intro he
  have hi := ((mem_colorNeighborhood _ _ _ _).mp (m.mem_neighborhood i)).2
  have hz := ((mem_colorNeighborhood _ _ _ _).mp hm).2
  rw [he,hz] at hi
  exact owner_ne_three side hi.symm

theorem support_image {n : Nat} {c : Host} {r mark : Vertex} {side : Bool}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) t)
    (hm : mark∈colorNeighborhood c (palette 3) r) :
    (support m mark).image m.vertex=attachingSupport c r (palette 3) mark (palette (owner side)) := by
  ext v
  constructor
  · rintro hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr
      ⟨vertex_ne_mark m hm i,(mem_filter.mp hi).2⟩,m.mem_neighborhood i⟩
  · intro hv
    obtain ⟨hmark,hroot⟩ := mem_inter.mp hv
    obtain ⟨i,rfl⟩ := m.covers_neighborhood v hroot
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,((mem_colorNeighborhood _ _ _ _).mp hmark).2⟩,rfl⟩

theorem support_independent {n : Nat} {c : Host} {r mark : Vertex} {side : Bool}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) t)
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hp : m.colors=foreignEquiv (owner side)) :
    ∀a∈support m mark,∀b∈support m mark,a≠b → t a b≠2 := by
  intro a ha b hb hab he
  have ha3 := (mem_filter.mp ha).2
  have hb3 := (mem_filter.mp hb).2
  have hab3 : c (m.vertex a) (m.vertex b)=palette 3 := by rw [m.map_color a b hab,hp,he,foreign_two]
  exact hc mark (m.vertex a) (m.vertex b)
    ⟨(vertex_ne_mark m hm a).symm,(vertex_ne_mark m hm b).symm,m.vertex.injective.ne hab⟩
    ⟨ha3.trans hb3.symm,hb3.trans hab3.symm⟩

/-- The whole foreign support has size four or five; no uncovered size is
silently dropped before applying the finite orbit table. -/
theorem support_four_or_five {n : Nat} {c : Host} {r mark : Vertex} {side : Bool}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) t)
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hh : 15≤colorDegree c (palette 3) mark) :
    (support m mark).card=4 ∨ (support m mark).card=5 := by
  obtain ⟨p0,p1,p2,_,_,_,heq,hpat⟩ := genuine_high_attaching_support_geometry c hc r (palette 3) mark hm hh
  have hmem : palette (owner side)∈({p0,p1,p2} : Finset FourColor) := by
    rw [←heq];cases side <;> decide
  have hcount : (support m mark).card=
      (attachingSupport c r (palette 3) mark (palette (owner side))).card := by
    rw [←support_image m hm,card_image_of_injective _ m.vertex.injective]
  rw [hcount]
  simp only [mem_insert,mem_singleton] at hmem
  unfold FourFivePattern at hpat
  rcases hmem with he|he|he <;> rw [he] <;> rcases hpat with h|h|h|h <;> omega

/-- Every actual four-point foreign support satisfies exactly the P4
predicate used by every U/T15/16 orbit table. The embedding covers the whole
physical support; this never replaces it by an arbitrary independent four-set. -/
theorem actual_four_is_proper {n : Nat} {c : Host} {r mark : Vertex} {side : Bool}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette (owner side)) t)
    (hc : NoMonochromaticTriangle c) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hp : m.colors=foreignEquiv (owner side)) (hh : 15≤colorDegree c (palette 3) mark)
    (hs : (support m mark).card=4) :
    (∀a∈support m mark,∀b∈support m mark,a≠b → t a b≠2) ∧
    (∀a∈support m mark,((support m mark).filter fun b=>b≠a ∧ t a b=0).card=1 ∨
      ((support m mark).filter fun b=>b≠a ∧ t a b=0).card=2) ∧
    ((support m mark).filter fun a=>((support m mark).filter fun b=>b≠a ∧ t a b=0).card=1).card=2 := by
  classical
  have hcard : (attachingSupport c r (palette 3) mark (palette (owner side))).card=4 := by
    rw [←support_image m hm,card_image_of_injective _ m.vertex.injective,hs]
  obtain ⟨e,he,hpath⟩ := actual_high_four_support_path c hc r mark hm hh side hcard
  change univ.image e=attachingSupport c r (palette 3) mark (palette (owner side)) at he
  have hem (i : Fin 4) : e i∈attachingSupport c r (palette 3) mark (palette (owner side)) := by
    rw [←he];exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have hinv : ∀i : Fin 4,∃j : Fin n,m.vertex j=e i := by
    intro i;exact m.covers_neighborhood (e i) (mem_inter.mp (hem i)).2
  choose f hf using hinv
  let z : Fin 4↪Fin n := ⟨f,fun i j h=>e.injective ((hf i).symm.trans ((congrArg m.vertex h).trans (hf j)))⟩
  have hz : univ.image z=support m mark := by
    ext j
    constructor
    · rintro h
      obtain ⟨i,_,rfl⟩ := mem_image.mp h
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      change c mark (m.vertex (f i))=palette 3
      rw [hf]
      exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp (hem i)).1).2
    · intro hj
      have hphys : m.vertex j∈attachingSupport c r (palette 3) mark (palette (owner side)) := by
        rw [←support_image m hm];exact mem_image.mpr ⟨j,hj,rfl⟩
      rw [←he] at hphys
      obtain ⟨i,_,hi⟩ := mem_image.mp hphys
      exact mem_image.mpr ⟨i,mem_univ _,m.vertex.injective ((hf i).trans hi)⟩
  have hzpath : ∀i j : Fin 4,i≠j → (t (z i) (z j)=0 ↔ PathAdjacent i j) := by
    intro i j hij
    have h := hpath i j hij
    rw [←hf i,←hf j] at h
    change c (m.vertex (z i)) (m.vertex (z j))=palette 0 ↔ PathAdjacent i j at h
    rw [m.map_color _ _ (z.injective.ne hij),hp,foreign_zero_iff] at h
    exact h
  exact ⟨support_independent m hc hm hp,path_four_degrees (fun a b=>t a b) (support m mark) z hz hzpath⟩

#print axioms support_independent
#print axioms support_four_or_five
#print axioms actual_four_is_proper
end PricingIntegration.PhysicalForeignSupport
