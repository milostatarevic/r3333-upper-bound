import PricingC.Rooted45Orientation

namespace PricingC.Rooted45Orientation
open R4333 PricingC.OwnFive15

theorem group_zero : ∀ k : Bool,∀ i : Fin 15,group k i=0 ↔ i.val<5 := by decide
theorem interior_own : ∀ k : Bool,∀ i j : Fin 5,interior k (label i) (label j)=canonical i j := by decide

theorem freeLift_group (k : Bool) (p : Equiv.Perm (Fin 5)) (i : Fin 15) :
 group k (freeLift p i)=group k i := by
 by_cases hi:i.val<5
 · have he:i=label ⟨i.val,hi⟩ := by rfl
   rw [he,freeLift_label]
   simp [group,label,hi]
 · rw [freeLift_ge5 p i (by omega)]

theorem free_normalization (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor)
 (hc:NoMonochromaticTriangle c) (h:ForeignCanonical k c) :
 ∃p:Equiv.Perm (Fin 5),Canonical k (relabelFree c p) := by
 obtain ⟨p,hp⟩:=free_C5_normalization c hc (by
  intro i hi
  rw [h.root_edges i hi]
  exact group_zero k i)
 refine ⟨p,?_,?_⟩
 · intro i hi
   change c (freeLift p 14) (freeLift p i)=_
   rw [freeLift_ge5 p 14 (by decide)]
   rw [h.root_edges _ (by
    intro hh
    apply hi
    exact (freeLift p).injective (hh.trans (freeLift_ge5 p 14 (by decide)).symm))]
   exact freeLift_group k p i
 · intro a b hab ha hb hg
   by_cases hz:group k a=0
   · have hal:= (group_zero k a).mp hz
     have hbl:=(group_zero k b).mp (hg.symm.trans hz)
     have hae:a=label ⟨a.val,hal⟩:=rfl
     have hbe:b=label ⟨b.val,hbl⟩:=rfl
     rw [hae,hbe,interior_own]
     exact hp _ _ (by intro hh;apply hab;exact congrArg label hh)
   · have hal:5≤a.val:=by have := (group_zero k a).not.mp hz;omega
     have hbl:5≤b.val:=by
      have hh:group k b≠0:=by intro hh;exact hz (hg.trans hh)
      have := (group_zero k b).not.mp hh
      omega
     change c (freeLift p a) (freeLift p b)=_
     rw [freeLift_ge5 p a hal,freeLift_ge5 p b hbl]
     exact h.foreign_edges a b hab ha hb hz hg

#print axioms free_normalization
end PricingC.Rooted45Orientation
