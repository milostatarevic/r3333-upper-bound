import UniformK61.UUActionsProof
import UniformK61.UUSourceSoundness

set_option autoImplicit false
set_option maxRecDepth 100000
namespace UniformK61.UUTemplateTransport
open Ramsey61 UniformK61.Core UniformK61.UUSourceDefs
open UniformK61.UUBridgeData PricingC.U15SupportCover
open PricingABD.ABGeometry

/-- The static root and template facts, independent of supports and words. -/
structure StaticHost (q : Bool) (c : Host) : Prop where
 spokes : ∀v : Vertex,v≠0 → c 0 v=palette (rootColor v)
 left : ∀u v : Fin 15,u≠v → c (lVertex u) (lVertex v)=palette (foreign 1 (R4333.k15Template false u v))
 right : ∀u v : Fin 15,u≠v → c (rVertex u) (rVertex v)=palette (foreign 2 (R4333.k15Template false u v))
 marked : ∀u v : Fin 16,u≠v → c (qVertex u) (qVertex v)=palette (foreign 3 (R4333.k16Template q u v))

theorem source_static {q : Bool} {p : UUSupportData.Pair} {i : Fin 600} {c : Host}
 (h : SourceWitness q p i c) : StaticHost q c := ⟨h.spokes,h.left,h.right,h.marked⟩

@[simp] theorem swap_zero : (Equiv.swap (1:Color) 2) 0=0 := by decide
@[simp] theorem swap_three : (Equiv.swap (1:Color) 2) 3=3 := by decide

theorem swapped_foreign_left : ∀k : Fin 3,
 (Equiv.swap (1:Color) 2) (foreign 1 k)=foreign 2 k := by decide +kernel

theorem swapped_foreign_right : ∀k : Fin 3,
 (Equiv.swap (1:Color) 2) (foreign 2 k)=foreign 1 k := by decide +kernel

set_option maxHeartbeats 0 in
theorem q_preserves : ∀q : Bool,∀u v : Fin 16,u≠v →
 foreign 3 (R4333.k16Template q (qBackward q u) (qBackward q v))=
 (Equiv.swap (1:Color) 2) (foreign 3 (R4333.k16Template q u v)) := by decide +kernel

theorem backward_root (a : Action) (q : Bool) : backward a q 0=0 := by simp [backward]

theorem backward_rootColor (a : Action) (q : Bool) (v : Vertex) :
 rootColor (backward a q v)=(colors a).symm (rootColor v) := by
 by_cases h0 : v.val=0
 · have he : v=0:=Fin.ext h0
   subst v
   cases hs : (row a).swapped <;> simp [backward,rootColor,colors,hs]
 by_cases h5 : v.val≤5
 · let x : Fin 5:=⟨v.val-1,by omega⟩
   have he : v=fVertex x := by apply Fin.ext;dsimp [fVertex,x];omega
   rw [he,backward_free]
   have h:=(freeMap (row a).freeInverse x).isLt
   have hx:=x.isLt
   cases hs : (row a).swapped <;> simp [rootColor,fVertex,colors,hs,show 1+x.val≤14 by omega,show 1+(freeMap (row a).freeInverse x).val≤14 by omega]
 by_cases h14 : v.val≤14
 · have hb : backward a q v=v:=by
     apply Fin.ext
     simp only [backward,Fin.val_mk]
     simp [h0,h5,h14,Nat.mod_eq_of_lt v.isLt]
   rw [hb]
   cases hs : (row a).swapped <;> simp [rootColor,colors,hs,h14]
 by_cases h29 : v.val≤29
 · let x : Fin 15:=⟨v.val-15,by omega⟩
   have he : v=lVertex x := by apply Fin.ext;dsimp [lVertex,x];omega
   rw [he,backward_left]
   have hx:=x.isLt
   have hl:=(autoMap (row a).leftInverse x).isLt
   have hr:=(autoMap (row a).rightInverse x).isLt
   cases hs : (row a).swapped <;> simp [hs,rootColor,colors,lVertex,rVertex] <;> split_ifs <;> simp_all only [swap_zero,swap_three,Equiv.swap_apply_left,Equiv.swap_apply_right] <;> omega
 by_cases h44 : v.val≤44
 · let x : Fin 15:=⟨v.val-30,by omega⟩
   have he : v=rVertex x := by apply Fin.ext;dsimp [rVertex,x];omega
   rw [he,backward_right]
   have hx:=x.isLt
   have hl:=(autoMap (row a).leftInverse x).isLt
   have hr:=(autoMap (row a).rightInverse x).isLt
   cases hs : (row a).swapped <;> simp [hs,rootColor,colors,lVertex,rVertex] <;> split_ifs <;> simp_all only [swap_zero,swap_three,Equiv.swap_apply_left,Equiv.swap_apply_right] <;> omega
 · let x : Fin 16:=⟨v.val-45,by have h:=v.isLt;omega⟩
   have he : v=qVertex x := by apply Fin.ext;dsimp [qVertex,x];omega
   rw [he,backward_q]
   have hx:=x.isLt
   have hr:=(qBackward q x).isLt
   cases hs : (row a).swapped <;> simp [hs,rootColor,colors,qVertex] <;> split_ifs <;> simp_all only [swap_zero,swap_three,Equiv.swap_apply_left,Equiv.swap_apply_right] <;> omega

theorem auto_template (a : Fin 10) (u v : Fin 15) (hne : u≠v) :
 R4333.k15Template false (autoMap a u) (autoMap a v)=R4333.k15Template false u v :=
 auto_preserves a u v hne

theorem static_transport {q : Bool} {c : Host} (h : StaticHost q c) (a : Action) :
 StaticHost q (UnitTransport.transformed c (vertices q a) (colors a)) := by
 refine ⟨?_,?_,?_,?_⟩
 · intro v hv
   apply (UnitTransport.transformed_color c (vertices q a) (colors a) 0 v _).mpr
   change c (backward a q 0) (backward a q v)=_
   have hn : backward a q v≠0 := by
     have hh := (vertices q a).injective.ne hv
     simpa only [vertices,Equiv.coe_fn_mk,backward_root] using hh
   rw [backward_root,h.spokes _ hn,backward_rootColor]
 · intro u v hne
   apply (UnitTransport.transformed_color c (vertices q a) (colors a) _ _ _).mpr
   change c (backward a q (lVertex u)) (backward a q (lVertex v))=_
   rw [backward_left,backward_left]
   cases hs : (row a).swapped
   · simp only [hs,Bool.false_eq_true,if_false,colors,Equiv.refl_symm,Equiv.refl_apply]
     rw [h.left _ _ ((auto_bijective _).injective.ne hne),auto_template _ _ _ hne]
   · simp only [hs,if_true,colors,Equiv.symm_swap]
     rw [h.right _ _ ((auto_bijective _).injective.ne hne),auto_template _ _ _ hne,swapped_foreign_left]
 · intro u v hne
   apply (UnitTransport.transformed_color c (vertices q a) (colors a) _ _ _).mpr
   change c (backward a q (rVertex u)) (backward a q (rVertex v))=_
   rw [backward_right,backward_right]
   cases hs : (row a).swapped
   · simp only [hs,Bool.false_eq_true,if_false,colors,Equiv.refl_symm,Equiv.refl_apply]
     rw [h.right _ _ ((auto_bijective _).injective.ne hne),auto_template _ _ _ hne]
   · simp only [hs,if_true,colors,Equiv.symm_swap]
     rw [h.left _ _ ((auto_bijective _).injective.ne hne),auto_template _ _ _ hne,swapped_foreign_right]
 · intro u v hne
   apply (UnitTransport.transformed_color c (vertices q a) (colors a) _ _ _).mpr
   change c (backward a q (qVertex u)) (backward a q (qVertex v))=_
   rw [backward_q,backward_q]
   cases hs : (row a).swapped
   · simpa only [hs,Bool.false_eq_true,if_false,colors,Equiv.refl_symm,Equiv.refl_apply] using h.marked u v hne
   · simp only [hs,if_true,colors,Equiv.symm_swap]
     have hn : qBackward q u≠qBackward q v := by
       intro he
       apply hne
       have hh:=congrArg (qForward q) he
       simpa only [(q_inverse q u).1,(q_inverse q v).1] using hh
     rw [h.marked _ _ hn,q_preserves q u v hne]

deriving instance DecidableEq for Core.PhysicalUnit

def simpleTemplates (q : Bool) : List PhysicalUnit :=
 ((orderedPairs 15).map fun ab => ⟨true,lVertex ab.1,lVertex ab.2,foreign 1 (R4333.k15Template false ab.1 ab.2)⟩) ++
 ((orderedPairs 15).map fun ab => ⟨true,rVertex ab.1,rVertex ab.2,foreign 2 (R4333.k15Template false ab.1 ab.2)⟩) ++
 ((orderedPairs 16).map fun ab => ⟨true,qVertex ab.1,qVertex ab.2,foreign 3 (R4333.k16Template q ab.1 ab.2)⟩)

set_option maxHeartbeats 0 in
theorem templates_eq : ∀q : Bool,MarkedUU.templateUnits q=simpleTemplates q := by decide +kernel

theorem spokes_match {q : Bool} {c : Host} (h : StaticHost q c) :
 UnitsMatch c ((List.finRange 60).map MarkedUU.spoke) := by
 intro u hu
 obtain ⟨v,_,rfl⟩:=List.mem_map.mp hu
 have hn : (0:Vertex)≠⟨v.val+1,by have hh:=v.isLt;omega⟩ := by
   intro he
   have hh:=congrArg Fin.val he
   simp only [Fin.val_zero] at hh
   omega
 exact ⟨hn,h.spokes _ hn.symm⟩

theorem ordered_ne {n : Nat} (ab : Fin n×Fin n) (h : ab∈orderedPairs n) : ab.1≠ab.2 := by
 simp only [orderedPairs,List.mem_flatMap,List.mem_map] at h
 obtain ⟨a,_,b,hb,rfl⟩:=h
 exact ne_of_lt (by simpa using (List.mem_filter.mp hb).2)

theorem templates_match {q : Bool} {c : Host} (h : StaticHost q c) :
 UnitsMatch c (MarkedUU.templateUnits q) := by
 rw [templates_eq]
 intro u hu
 simp only [simpleTemplates,List.mem_append] at hu
 rcases hu with (hu|hu)|hu
 · obtain ⟨ab,hab,rfl⟩:=List.mem_map.mp hu
   have hn:=ordered_ne ab hab
   refine ⟨?_,h.left _ _ hn⟩
   intro he
   apply hn
   apply Fin.ext
   have hh:=congrArg Fin.val he
   simp only [lVertex,Fin.val_mk] at hh
   omega
 · obtain ⟨ab,hab,rfl⟩:=List.mem_map.mp hu
   have hn:=ordered_ne ab hab
   refine ⟨?_,h.right _ _ hn⟩
   intro he
   apply hn
   apply Fin.ext
   have hh:=congrArg Fin.val he
   simp only [rVertex,Fin.val_mk] at hh
   omega
 · obtain ⟨ab,hab,rfl⟩:=List.mem_map.mp hu
   have hn:=ordered_ne ab hab
   refine ⟨?_,h.marked _ _ hn⟩
   intro he
   apply hn
   apply Fin.ext
   have hh:=congrArg Fin.val he
   simp only [qVertex,Fin.val_mk] at hh
   omega

/-- All 390 static facts follow generically from the one global action.
Only the support, word and membership tail needs casewise finite checking. -/
theorem static_units_match {q : Bool} {p : UUSupportData.Pair} {i : Fin 600} {c : Host}
 (h : SourceWitness q p i c) (a : Action) :
 UnitsMatch (UnitTransport.transformed c (vertices q a) (colors a))
  ((List.finRange 60).map MarkedUU.spoke ++ MarkedUU.templateUnits q) := by
 intro u hu
 rcases List.mem_append.mp hu with hu|hu
 · exact spokes_match (static_transport (source_static h) a) u hu
 · exact templates_match (static_transport (source_static h) a) u hu

#print axioms static_units_match
end UniformK61.UUTemplateTransport
