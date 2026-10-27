import UniformK61.UUActions

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace UniformK61.UUBridgeData
open UniformK61.Core PricingC.U15SupportCover

def fVertex (v : Fin 5) : Vertex := ⟨1+v.val,by omega⟩
def lVertex (v : Fin 15) : Vertex := ⟨15+v.val,by omega⟩
def rVertex (v : Fin 15) : Vertex := ⟨30+v.val,by omega⟩
def qVertex (v : Fin 16) : Vertex := ⟨45+v.val,by omega⟩
def freeMap (code : Nat) (v : Fin 5) : Fin 5 :=
 ⟨freeDigit code v.val,Nat.mod_lt _ (by decide)⟩

theorem forward_free (a : Action) (q : Bool) (v : Fin 5) :
 forward a q (fVertex v)=fVertex (freeMap (row a).freeCode v) := by
 apply Fin.ext
 have h := (freeMap (row a).freeCode v).isLt
 fin_cases v <;> simp [forward,fVertex,freeMap] at * <;> omega

theorem forward_left (a : Action) (q : Bool) (v : Fin 15) :
 forward a q (lVertex v)=
 if (row a).swapped then rVertex (autoMap (row a).leftAuto v)
 else lVertex (autoMap (row a).leftAuto v) := by
 have h := (autoMap (row a).leftAuto v).isLt
 cases hs : (row a).swapped <;> apply Fin.ext <;>
   fin_cases v <;> simp [forward,lVertex,rVertex,hs] at * <;> omega


theorem backward_free (a : Action) (q : Bool) (v : Fin 5) :
 backward a q (fVertex v)=fVertex (freeMap (row a).freeInverse v) := by
 apply Fin.ext
 have h := (freeMap (row a).freeInverse v).isLt
 fin_cases v <;> simp [backward,fVertex,freeMap] at * <;> omega

theorem forward_right (a : Action) (q : Bool) (v : Fin 15) :
 forward a q (rVertex v)=
 if (row a).swapped then lVertex (autoMap (row a).rightAuto v)
 else rVertex (autoMap (row a).rightAuto v) := by
 have h := (autoMap (row a).rightAuto v).isLt
 cases hs : (row a).swapped <;> apply Fin.ext <;>
   fin_cases v <;> simp [forward,lVertex,rVertex,hs] at * <;> omega

theorem backward_left (a : Action) (q : Bool) (v : Fin 15) :
 backward a q (lVertex v)=
 if (row a).swapped then rVertex (autoMap (row a).rightInverse v)
 else lVertex (autoMap (row a).leftInverse v) := by
 have hl := (autoMap (row a).leftInverse v).isLt
 have hr := (autoMap (row a).rightInverse v).isLt
 cases hs : (row a).swapped <;> apply Fin.ext <;>
   fin_cases v <;> simp [backward,lVertex,rVertex,hs] at * <;> omega

theorem backward_right (a : Action) (q : Bool) (v : Fin 15) :
 backward a q (rVertex v)=
 if (row a).swapped then lVertex (autoMap (row a).leftInverse v)
 else rVertex (autoMap (row a).rightInverse v) := by
 have hl := (autoMap (row a).leftInverse v).isLt
 have hr := (autoMap (row a).rightInverse v).isLt
 cases hs : (row a).swapped <;> apply Fin.ext <;>
   fin_cases v <;> simp [backward,lVertex,rVertex,hs] at * <;> omega

theorem forward_q (a : Action) (q : Bool) (v : Fin 16) :
 forward a q (qVertex v)=
 if (row a).swapped then qVertex (qForward q v) else qVertex v := by
 have h := (qForward q v).isLt
 cases hs : (row a).swapped <;> apply Fin.ext <;>
   fin_cases v <;> simp [forward,qVertex,hs] at * <;> omega

theorem backward_q (a : Action) (q : Bool) (v : Fin 16) :
 backward a q (qVertex v)=
 if (row a).swapped then qVertex (qBackward q v) else qVertex v := by
 have h := (qBackward q v).isLt
 cases hs : (row a).swapped <;> apply Fin.ext <;>
   fin_cases v <;> simp [backward,qVertex,hs] at * <;> omega

theorem freeMap_inverse (a : Action) (v : Fin 5) :
 freeMap (row a).freeCode (freeMap (row a).freeInverse v)=v ∧
 freeMap (row a).freeInverse (freeMap (row a).freeCode v)=v := by
 have h:=free_inverse ((row a).freeCode,(row a).freeInverse) (rows_ok a).1 v
 exact ⟨Fin.ext h.1,Fin.ext h.2⟩

theorem action_inverse (a : Action) (q : Bool) (v : Vertex) :
 forward a q (backward a q v)=v ∧ backward a q (forward a q v)=v := by
 by_cases h0 : v.val=0
 · have he : v=0:=Fin.ext h0
   subst v
   simp [forward,backward]
 by_cases h5 : v.val≤5
 · let x : Fin 5:=⟨v.val-1,by omega⟩
   have he : v=fVertex x := by apply Fin.ext;dsimp [fVertex,x];omega
   rw [he,backward_free,forward_free,forward_free,backward_free]
   exact ⟨congrArg fVertex (freeMap_inverse a x).1,
     congrArg fVertex (freeMap_inverse a x).2⟩
 by_cases h14 : v.val≤14
 · have hf : forward a q v=v:=by
     apply Fin.ext
     simp only [forward,Fin.val_mk]
     simp [h0,h5,h14,Nat.mod_eq_of_lt v.isLt]
   have hb : backward a q v=v:=by
     apply Fin.ext
     simp only [backward,Fin.val_mk]
     simp [h0,h5,h14,Nat.mod_eq_of_lt v.isLt]
   exact ⟨by rw [hb,hf],by rw [hf,hb]⟩
 by_cases h29 : v.val≤29
 · let x : Fin 15:=⟨v.val-15,by omega⟩
   have he : v=lVertex x := by apply Fin.ext;dsimp [lVertex,x];omega
   rw [he]
   cases hs : (row a).swapped <;>
     simp only [backward_left,forward_left,forward_right,backward_right,hs,Bool.false_eq_true,
       if_false,if_true,(rows_ok a).2.1,(rows_ok a).2.2] <;>
     simp only [(auto_inverse (row a).leftAuto x).1,(auto_inverse (row a).leftAuto x).2,
       (auto_inverse (row a).rightAuto x).1,and_self]
 by_cases h44 : v.val≤44
 · let x : Fin 15:=⟨v.val-30,by omega⟩
   have he : v=rVertex x := by apply Fin.ext;dsimp [rVertex,x];omega
   rw [he]
   cases hs : (row a).swapped <;>
     simp only [backward_left,forward_left,forward_right,backward_right,hs,Bool.false_eq_true,
       if_false,if_true,(rows_ok a).2.1,(rows_ok a).2.2] <;>
     simp only [(auto_inverse (row a).leftAuto x).1,
       (auto_inverse (row a).rightAuto x).1,(auto_inverse (row a).rightAuto x).2,and_self]
 · let x : Fin 16:=⟨v.val-45,by have h:=v.isLt;omega⟩
   have he : v=qVertex x := by apply Fin.ext;dsimp [qVertex,x];omega
   rw [he]
   cases hs : (row a).swapped <;>
     simp only [forward_q,backward_q,hs,Bool.false_eq_true,if_false,if_true,
       (q_inverse q x).1,(q_inverse q x).2,and_self]

def vertices (q : Bool) (a : Action) : Vertex ≃ Vertex where
 toFun:=backward a q
 invFun:=forward a q
 left_inv v:=(action_inverse a q v).1
 right_inv v:=(action_inverse a q v).2

def colors (a : Action) : Color ≃ Color :=
 if (row a).swapped then Equiv.swap 1 2 else Equiv.refl _

#print axioms action_inverse
end UniformK61.UUBridgeData
