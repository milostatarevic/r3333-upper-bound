import UniformK60.UUMarkedOmission
import UniformK60.UUFiniteBridge
import UniformK61.UUResidualTransport

/-! Move the omitted marked position within its existing mark stabilizer.
All sixty retained vertices move together; no good61 extension is used. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.UUMarkedTransport
open Ramsey61 UniformK61.Core UniformK61.UUBridgeData
open UniformK61.UUTemplateTransport UniformK60.UUMarkedOmission

def liftMap (e : Fin 16 ≃ Fin 16) (v : Vertex) : Vertex :=
  if h : v.val<45 then v
  else qVertex (e ⟨v.val-45,by have := v.isLt;omega⟩)

theorem lift_small (e : Fin 16 ≃ Fin 16) (v : Vertex) (h : v.val≤44) :
    liftMap e v=v := by simp [liftMap,show v.val<45 by omega]

theorem lift_q (e : Fin 16 ≃ Fin 16) (v : Fin 16) :
    liftMap e (qVertex v)=qVertex (e v) := by
  simp [liftMap,qVertex]

theorem lift_inverse (e : Fin 16 ≃ Fin 16) (v : Vertex) :
    liftMap e.symm (liftMap e v)=v := by
  by_cases h : v.val≤44
  · rw [lift_small _ _ h,lift_small _ _ h]
  · let a : Fin 16 := ⟨v.val-45,by have := v.isLt;omega⟩
    have hv : v=qVertex a := by apply Fin.ext;dsimp [qVertex,a];omega
    rw [hv,lift_q,lift_q,e.symm_apply_apply]

def liftEquiv (e : Fin 16 ≃ Fin 16) : Vertex ≃ Vertex where
  toFun := liftMap e
  invFun := liftMap e.symm
  left_inv := lift_inverse e
  right_inv := lift_inverse e.symm

noncomputable def vertices (q : Bool) (r : Fin 15) : Vertex ≃ Vertex :=
  liftEquiv (localEquiv q r)

theorem small (q : Bool) (r : Fin 15) (v : Vertex) (hv : v.val≤44) :
    vertices q r v=v := lift_small _ _ hv

theorem marked (q : Bool) (r : Fin 15) (v : Fin 16) :
    vertices q r (qVertex v)=qVertex (localBackward q r v) := lift_q _ _

theorem mark (q : Bool) (r : Fin 15) : vertices q r 60=60 := by
  change vertices q r (qVertex 15)=qVertex 15
  rw [marked,fixes_mark]

theorem local_rootColor (q : Bool) (r : Fin 15) (v : Vertex) :
    UniformK61.UUSourceDefs.rootColor (vertices q r v)=UniformK61.UUSourceDefs.rootColor v := by
  by_cases h : v.val≤44
  · rw [small _ _ _ h]
  · let a : Fin 16 := ⟨v.val-45,by have := v.isLt;omega⟩
    have hv : v=qVertex a := by apply Fin.ext;dsimp [qVertex,a];omega
    rw [hv,marked]
    simp only [UniformK61.UUSourceDefs.rootColor,qVertex,Fin.val_mk]
    split_ifs <;> first | rfl | omega

theorem static {q : Bool} {c : Host} (h : StaticHost q c) (r : Fin 15) :
    StaticHost q (UniformK61.UnitTransport.transformed c (vertices q r) (Equiv.refl _)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv
    apply (UniformK61.UnitTransport.transformed_color _ _ _ _ _ _).mpr
    simp only [Equiv.refl_symm,Equiv.refl_apply,small q r 0 (by decide)]
    have hn : vertices q r v≠0 := by
      simpa only [small q r 0 (by decide)] using (vertices q r).injective.ne hv
    rw [h.spokes _ hn,local_rootColor]
  · intro a b hab
    apply (UniformK61.UnitTransport.transformed_color _ _ _ _ _ _).mpr
    have ha : (lVertex a).val≤44 := by dsimp [lVertex];omega
    have hb : (lVertex b).val≤44 := by dsimp [lVertex];omega
    simpa only [small q r _ ha,small q r _ hb,Equiv.refl_symm,Equiv.refl_apply] using h.left a b hab
  · intro a b hab
    apply (UniformK61.UnitTransport.transformed_color _ _ _ _ _ _).mpr
    have ha : (rVertex a).val≤44 := by dsimp [rVertex];omega
    have hb : (rVertex b).val≤44 := by dsimp [rVertex];omega
    simpa only [small q r _ ha,small q r _ hb,Equiv.refl_symm,Equiv.refl_apply] using h.right a b hab
  · intro a b hab
    apply (UniformK61.UnitTransport.transformed_color _ _ _ _ _ _).mpr
    simp only [marked,Equiv.refl_symm,Equiv.refl_apply]
    rw [h.marked _ _ ((local_bijective q r).injective.ne hab),local_preserves q r a b hab]

theorem negative_color (j : UniformK61.MarkedUU.Leaf) (u : PhysicalUnit)
    (hu : u∈residualUnits j) (hp : u.positive=false) : u.q=3 := by
  simp only [residualUnits,List.mem_append] at hu
  rcases hu with (hu|hu)|hu
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hu
    simp at hp
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hu
    simp at hp
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hu
    rfl

theorem units {q : Bool} {c : Host} (h : StaticHost q c)
    (j : UniformK61.MarkedUU.Leaf) (hj : UnitsMatch c (UniformK61.MarkedUU.caseUnits q j))
    (r : Fin 15) : UnitsMatch
      (UniformK61.UnitTransport.transformed c (vertices q r) (Equiv.refl _))
      (UniformK61.MarkedUU.caseUnits q j) := by
  let d := UniformK61.UnitTransport.transformed c (vertices q r) (Equiv.refl _)
  have hd := static h r
  intro u hu
  have he : UniformK61.MarkedUU.caseUnits q j=
      ((List.finRange 60).map UniformK61.MarkedUU.spoke ++ UniformK61.MarkedUU.templateUnits q) ++
      residualUnits j := by simp only [UniformK61.MarkedUU.caseUnits,residualUnits,List.append_assoc]
  have hold := hj u hu
  rw [he] at hu
  rcases List.mem_append.mp hu with hu|hu
  · rcases List.mem_append.mp hu with hu|hu
    · exact spokes_match hd u hu
    · exact templates_match hd u hu
  · rcases UniformK61.UUResidualTransport.residual_safe j u hu with ⟨ha,hb⟩|⟨hb,ha⟩
    · apply UniformK61.UnitTransport.related_matches c (vertices q r) (Equiv.refl _) u u hold
      exact ⟨rfl,rfl,Or.inl ⟨(small _ _ _ ha).symm,(small _ _ _ hb).symm⟩⟩
    · rcases ha with ha|⟨hp,hlo,hhi⟩
      · apply UniformK61.UnitTransport.related_matches c (vertices q r) (Equiv.refl _) u u hold
        refine ⟨rfl,rfl,Or.inl ⟨(small _ _ _ ha).symm,?_⟩⟩
        rw [hb,mark]
      · have hq := negative_color j u hu hp
        let a : Fin 16 := ⟨u.u.val-45,by omega⟩
        have ha : u.u=qVertex a := by apply Fin.ext;dsimp [qVertex,a];omega
        have han : a≠15 := by intro he;have := congrArg Fin.val he;dsimp [a] at this;omega
        refine ⟨hold.1,?_⟩
        change if u.positive then d u.u u.v=palette u.q else d u.u u.v≠palette u.q
        rw [hp,hq,hb,ha]
        simp only [Bool.false_eq_true,if_false]
        have hm := hd.marked a 15 han
        change d (qVertex a) (qVertex 15)≠palette 3
        rw [hm]
        exact fun hh => PricingABD.ABGeometry.foreign_ne 3 _ (CEncodingCore.palette_injective hh)

theorem omission (q : Bool) (r : Fin 15) :
    vertices q r (EFormula.omission q (index q r)).castSucc=qVertex r.castSucc := by
  change vertices q r (qVertex (EFormula.omissionPosition q (index q r)).castSucc)=qVertex r.castSucc
  rw [marked,moves_omission]

#print axioms units
end UniformK60.UUMarkedTransport
