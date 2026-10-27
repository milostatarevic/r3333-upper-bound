import UniformK61.PhysicalHelpers
import UniformK61.UUBridgeData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace UniformK61.UUResidualTransport
open UniformK61.Core UniformK61.UUSupportData UniformK61.UUSourceDefs
open UniformK61.UUBridgeData PricingC.U15SupportCover

theorem backward_small (a : Action) (q r : Bool) (v : Vertex) (hv : v.val≤44) :
 backward a q v=backward a r v := by
 unfold backward
 split_ifs <;> rfl

theorem backward_small_bound (a : Action) (q : Bool) (v : Vertex) (hv : v.val≤44) :
 (backward a q v).val≤44 := by
 have hfree : freeDigit (row a).freeInverse (v.val-1)<5:=Nat.mod_lt _ (by decide)
 have hl := (autoMap (if (row a).swapped then (row a).rightInverse else (row a).leftInverse)
   ⟨(v.val-15)%15,Nat.mod_lt _ (by decide)⟩).isLt
 have hr := (autoMap (if (row a).swapped then (row a).leftInverse else (row a).rightInverse)
   ⟨(v.val-30)%15,Nat.mod_lt _ (by decide)⟩).isLt
 simp only [backward,Fin.val_mk]
 split_ifs <;> omega

theorem backward_mark (a : Action) (q : Bool) : backward a q 60=60 := by
 have h:=backward_q a q 15
 have hh : qBackward q 15=15:=by cases q <;> decide
 have hq : qVertex 15=(60:Vertex):=by decide
 simpa only [hh,ite_self,hq] using h

theorem backward_qrange (a : Action) (q : Bool) (v : Vertex)
 (hlo : 45≤v.val) (hhi : v.val<60) :
 45≤(backward a q v).val ∧ (backward a q v).val<60 := by
 let x : Fin 16:=⟨v.val-45,by have:=v.isLt;omega⟩
 have he : v=qVertex x:=by apply Fin.ext;dsimp[qVertex,x];omega
 have hfix : qBackward q 15=15:=by cases q <;> decide
 have hne : qBackward q x≠15 := by
  intro h
  have hh:=congrArg (qForward q) h
  rw [(q_inverse q x).1] at hh
  have hfix' : qForward q 15=15:=by cases q <;> decide
  rw [hfix'] at hh
  have hval:=congrArg Fin.val hh
  dsimp[x] at hval
  omega
 have hq := (qBackward q x).isLt
 have hlt : (qBackward q x).val<15:=by
  have hn : (qBackward q x).val≠15:=fun h=>hne (Fin.ext h)
  omega
 rw [he,backward_q]
 split_ifs <;> simp only [qVertex,Fin.val_mk] <;> constructor <;> dsimp[x] at * <;> omega

theorem fixedColor_q (p : Pair) (i : Fin 600) (a b : Vertex) (ha : a.val<45) :
 fixedColor true p i a b=fixedColor false p i a b := by
 unfold fixedColor
 split_ifs <;> try rfl
 omega

theorem sourceFact_q_small (p : Pair) (i : Fin 600) (u : PhysicalUnit)
 (h : (min u.u u.v).val<45) : sourceFact true p i u=sourceFact false p i u := by
 unfold sourceFact
 dsimp only
 rw [fixedColor_q p i _ _ h]

theorem member_high (p : Pair) (v : Vertex) (h : 45≤v.val) : member p v=false := by
 have hf : (shape p).free≤5:=by cases shape p <;> decide
 unfold member
 split_ifs <;> first | rfl | omega

theorem negative_mark (q : Bool) (p : Pair) (i : Fin 600) (v : Vertex) (color : Color)
 (hlo : 45≤v.val) (hhi : v.val<60) :
 sourceFact q p i ⟨false,v,60,color⟩=(color==3) := by
 have hlt : v<(60:Vertex):=hhi
 have hm:=member_high p v hlo
 simp [sourceFact,min_eq_left (le_of_lt hlt),max_eq_right (le_of_lt hlt),hlt,hm]

def Safe (u : PhysicalUnit) : Prop :=
 (u.u.val≤44 ∧u.v.val≤44) ∨
 (u.v=60 ∧(u.u.val≤44 ∨(u.positive=false ∧45≤u.u.val ∧u.u.val<60)))
instance (u : PhysicalUnit) : Decidable (Safe u) := by unfold Safe;infer_instance

theorem pulled_q (p : Pair) (i : Fin 600) (a : Action) (u : PhysicalUnit) (h : Safe u) :
 sourceFact true p i (pulledUnit true a u)=sourceFact false p i (pulledUnit false a u) := by
 rcases h with ⟨hu,hv⟩|⟨hv,hu⟩
 · have eu:=backward_small a true false u.u hu
   have ev:=backward_small a true false u.v hv
   change sourceFact true p i ⟨u.positive,backward a true u.u,backward a true u.v,(colors a).symm u.q⟩=
     sourceFact false p i ⟨u.positive,backward a false u.u,backward a false u.v,(colors a).symm u.q⟩
   rw [eu,ev]
   apply sourceFact_q_small
   have hh:=backward_small_bound a false u.u hu
   have hm:=min_le_left (backward a false u.u) (backward a false u.v)
   change (min (backward a false u.u) (backward a false u.v)).val<45
   have hm':=(show (min (backward a false u.u) (backward a false u.v)).val≤
     (backward a false u.u).val from hm)
   omega
 · rcases hu with hu|⟨hp,hlo,hhi⟩
   · change sourceFact true p i ⟨u.positive,backward a true u.u,backward a true u.v,(colors a).symm u.q⟩=
       sourceFact false p i ⟨u.positive,backward a false u.u,backward a false u.v,(colors a).symm u.q⟩
     rw [hv,backward_mark,backward_mark,backward_small a true false u.u hu]
     apply sourceFact_q_small
     have hh:=backward_small_bound a false u.u hu
     have hm : (min (backward a false u.u) (60:Vertex)).val≤(backward a false u.u).val:=min_le_left _ _
     change (min (backward a false u.u) (60:Vertex)).val<45
     omega
   · change sourceFact true p i ⟨u.positive,backward a true u.u,backward a true u.v,(colors a).symm u.q⟩=
       sourceFact false p i ⟨u.positive,backward a false u.u,backward a false u.v,(colors a).symm u.q⟩
     rw [hv,hp,backward_mark,backward_mark]
     have ht:=backward_qrange a true u.u hlo hhi
     have hf:=backward_qrange a false u.u hlo hhi
     rw [negative_mark true p i _ _ ht.1 ht.2,negative_mark false p i _ _ hf.1 hf.2]


theorem free_size_le (j : MarkedUU.Leaf) : MarkedUU.freeSize j≤5 := by
 unfold MarkedUU.freeSize UUData.freeSize
 split_ifs <;> omega

theorem residual_safe (j : MarkedUU.Leaf) (u : PhysicalUnit) (hu : u∈residualUnits j) : Safe u := by
 simp only [residualUnits,List.mem_append] at hu
 rcases hu with (hu|hu)|hu
 · obtain ⟨⟨⟨a,b⟩,n⟩,hn,rfl⟩ := List.mem_map.mp hu
   have hab:=List.fst_mem_of_mem_zipIdx hn
   obtain ⟨ha,hb,_⟩:=UniformK61.PhysicalHelpers.mem_edges_bounds hab
   have hf:=free_size_le j
   apply Or.inl
   change (a+1)%61≤44 ∧ (b+1)%61≤44
   constructor <;> omega
 · obtain ⟨⟨⟨a,b⟩,n⟩,hn,rfl⟩ := List.mem_map.mp hu
   have hab:=List.fst_mem_of_mem_zipIdx hn
   have hf:=free_size_le j
   have hleft : ∀x∈MarkedUU.leftSupport j,x<15 := by
     intro x hx
     exact List.mem_range.mp (List.mem_filter.mp hx).1
   have hright : ∀x∈MarkedUU.rightSupport j,x<15 := by
     intro x hx
     exact List.mem_range.mp (List.mem_filter.mp hx).1
   have bounds : a≤44 ∧b≤44 := by
     simp only [MarkedUU.crossPairs,List.mem_append,List.mem_flatMap,List.mem_map] at hab
     rcases hab with ⟨x,hx,hb⟩|⟨x,hx,y,hy,he⟩
     · have hx:=List.mem_range.mp hx
       rcases hb with ⟨y,hy,he⟩|⟨y,hy,he⟩
       · cases he
         have hy:=hleft y hy
         constructor <;> omega
       · cases he
         have hy:=hright y hy
         constructor <;> omega
     · cases he
       have hx:=hleft x hx
       have hy:=hright y hy
       constructor <;> omega
   apply Or.inl
   change a%61≤44 ∧b%61≤44
   constructor <;> omega
 · obtain ⟨z,_,rfl⟩:=List.mem_map.mp hu
   apply Or.inr
   refine ⟨rfl,?_⟩
   by_cases h : z.val+1≤44
   · exact Or.inl h
   · apply Or.inr
     have hz:=z.isLt
     have hf:=free_size_le j
     change MarkedUU.markedMember j (z.val+1)=false ∧45≤z.val+1 ∧z.val+1<60
     refine ⟨?_,by omega,by omega⟩
     simp [MarkedUU.markedMember,
       show ¬z.val+1≤MarkedUU.freeSize j by omega,show 45≤z.val+1 by omega]

theorem residual_q (p : Pair) (i : Fin 600) (a : Action) (j : MarkedUU.Leaf)
 (u : PhysicalUnit) (hu : u∈residualUnits j) :
 sourceFact true p i (pulledUnit true a u)=sourceFact false p i (pulledUnit false a u) :=
 pulled_q p i a u (residual_safe j u hu)

theorem checkResidual_q (p : Pair) (i : Fin 600) : checkResidual true p i=checkResidual false p i := by
 unfold checkResidual
 apply Bool.eq_iff_iff.mpr
 simp only [List.all_eq_true]
 constructor
 · intro h u hu
   rw [←residual_q p i (action p i) (UUData.leaf (target p i)) u hu]
   exact h u hu
 · intro h u hu
   rw [residual_q p i (action p i) (UUData.leaf (target p i)) u hu]
   exact h u hu

#print axioms checkResidual_q
end UniformK61.UUResidualTransport
