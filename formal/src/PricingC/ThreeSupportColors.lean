import PricingC.ThreeSupportFrame
namespace PricingC.ThreeSupportFrame
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.P15PhysicalRooted (threeIndex)
open PricingC.Rooted45Orientation (Cycle)

def group {nf nl nr:Nat} (i:Fin (order nf nl nr)):Fin 3:=
 if i.val<nf then 0 else if i.val<nf+nl then 1 else 2

theorem group_free {nf nl nr:Nat} (i:Fin nf):group (label0 (nl:=nl) (nr:=nr) i)=0:=by
 simp[group,label0,i.isLt]
theorem group_left {nf nl nr:Nat} (i:Fin nl):group (label1 (nf:=nf) (nr:=nr) i)=1:=by
 simp only[group,label1]
 rw[if_neg (by omega),if_pos (by omega)]
theorem group_right {nf nl nr:Nat} (i:Fin nr):group (label2 (nf:=nf) (nl:=nl) i)=2:=by
 simp only[group,label2]
 rw[if_neg (by omega),if_neg (by omega)]

theorem restored_root_edges {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr):
 ∀i,i≠rootLabel nf nl nr → restoredColoring f (rootLabel nf nl nr) i=group i:=by
 intro i hi
 rcases label_cases i with rfl|⟨j,rfl⟩|⟨j,rfl⟩|⟨j,rfl⟩
 · exact False.elim (hi rfl)
 · change threeIndex (c (physical f (rootLabel nf nl nr)) (physical f (label0 j)))=_
   rw[physical_root,physical_free,((mem_colorNeighborhood _ _ _ _).mp (f.free_mem j)).2,group_free]
   rfl
 · change threeIndex (c (physical f (rootLabel nf nl nr)) (physical f (label1 j)))=_
   rw[physical_root,physical_left,((mem_colorNeighborhood _ _ _ _).mp (f.left_mem j)).2,group_left]
   rfl
 · change threeIndex (c (physical f (rootLabel nf nl nr)) (physical f (label2 j)))=_
   rw[physical_root,physical_right,((mem_colorNeighborhood _ _ _ _).mp (f.right_mem j)).2,group_right]
   rfl

theorem restored_left_edges {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr) (i j:Fin nl) (hij:i≠j):
 restoredColoring f (label1 i) (label1 j)=(if Cycle nl i.val j.val then (0:Fin 3) else 2):=by
 change threeIndex (c (physical f (label1 i)) (physical f (label1 j)))=_
 rw[physical_left,physical_left,f.left_edges i j hij]
 split_ifs <;> rfl

theorem restored_right_edges {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr) (i j:Fin nr) (hij:i≠j):
 restoredColoring f (label2 i) (label2 j)=(if Cycle nr i.val j.val then (0:Fin 3) else 1):=by
 change threeIndex (c (physical f (label2 i)) (physical f (label2 j)))=_
 rw[physical_right,physical_right,f.right_edges i j hij]
 split_ifs <;> rfl

theorem canonical_left_five : ∀i j:Fin 5,
 (if Cycle 5 i.val j.val then (0:Fin 3) else 2)=PricingABD.Rooted455Data.canonical1 i j ∧
 (if Cycle 5 i.val j.val then (0:Fin 3) else 2)=PricingC.Rooted555.canonical1 i j:=by decide

theorem canonical_right_five : ∀i j:Fin 5,
 (if Cycle 5 i.val j.val then (0:Fin 3) else 1)=PricingABD.Rooted455Data.canonical2 i j ∧
 (if Cycle 5 i.val j.val then (0:Fin 3) else 1)=PricingC.Rooted555.canonical2 i j:=by decide

theorem label0_injective {nf nl nr:Nat}:Function.Injective (label0 (nf:=nf) (nl:=nl) (nr:=nr)):=by
 intro i j h;apply Fin.ext;exact congrArg (fun x:Fin (order nf nl nr)=>x.val) h

theorem label1_injective {nf nl nr:Nat}:Function.Injective (label1 (nf:=nf) (nl:=nl) (nr:=nr)):=by
 intro i j h;apply Fin.ext;have:=congrArg (fun x:Fin (order nf nl nr)=>x.val) h;dsimp[label1] at this;omega

theorem label2_injective {nf nl nr:Nat}:Function.Injective (label2 (nf:=nf) (nl:=nl) (nr:=nr)):=by
 intro i j h;apply Fin.ext;have:=congrArg (fun x:Fin (order nf nl nr)=>x.val) h;dsimp[label2] at this;omega

#print axioms restored_root_edges
end PricingC.ThreeSupportFrame
