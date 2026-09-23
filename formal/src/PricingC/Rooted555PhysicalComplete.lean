import PricingC.Rooted555Catalogue
import PricingC.Rooted555Physical

namespace PricingC.Rooted555
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.P15PhysicalRooted (threeIndex threeIndex_palette palette_threeIndex)

theorem restored_spokes {c : Host} (f : Physical555 c) :
 ∀ i,i≠15 → restoredColoring f 15 i=group i := by
 intro i hi
 rcases label_cases i with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
 · exact False.elim (hi rfl)
 · change threeIndex (c (physical f 15) (physical f (label0 i)))=_
   rw [physical_root,physical_own,((mem_colorNeighborhood _ _ _ _).mp (f.own_mem i)).2,group_label0]
   rfl
 · change threeIndex (c (physical f 15) (physical f (label1 i)))=_
   rw [physical_root,physical_left,((mem_colorNeighborhood _ _ _ _).mp (f.left_mem i)).2,group_label1]
   rfl
 · change threeIndex (c (physical f 15) (physical f (label2 i)))=_
   rw [physical_root,physical_right,((mem_colorNeighborhood _ _ _ _).mp (f.right_mem i)).2,group_label2]
   rfl

theorem restored_foreign_one {c : Host} (f : Physical555 c) :
 ∀ i j,i≠j → restoredColoring f (label1 i) (label1 j)=canonical1 i j := by
 intro i j hij
 change threeIndex (c (physical f (label1 i)) (physical f (label1 j)))=_
 rw [physical_left,physical_left,f.left_edges i j hij,threeIndex_palette]

theorem restored_foreign_two {c : Host} (f : Physical555 c) :
 ∀ i j,i≠j → restoredColoring f (label2 i) (label2 j)=canonical2 i j := by
 intro i j hij
 change threeIndex (c (physical f (label2 i)) (physical f (label2 j)))=_
 rw [physical_right,physical_right,f.right_edges i j hij,threeIndex_palette]

theorem reordered_preserves_root_foreign {c : Host} (f : Physical555 c)
 (p : Equiv.Perm (Fin 5)) :
 physical f (freeLift p 15)=f.root ∧
 (∀ i,physical f (freeLift p (label1 i))=f.left i) ∧
 (∀ i,physical f (freeLift p (label2 i))=f.right i) := by
 refine ⟨?_,?_,?_⟩
 · rw [freeLift_ge5 p 15 (by decide),physical_root]
 · intro i
   rw [freeLift_ge5 p _ (by dsimp [label1];omega),physical_left]
 · intro i
   rw [freeLift_ge5 p _ (by dsimp [label2];omega),physical_right]

/-- Actual physical555 incidences supply one of the exact600 native75-trit
words. Only the same five free vertices are reordered; both foreign supports,
the root, the marked owner and every physical color stay unchanged. -/
theorem physical_host_to_exact600 {c : Host} (f : Physical555 c)
 (hc : NoMonochromaticTriangle c) :
 ∃ p : Equiv.Perm (Fin 5),∃ i : Fin 600,∀ a b : Fin 15,a≠b →
 c (physical f (freeLift p a.castSucc)) (physical f (freeLift p b.castSucc)) =
  palette (matrix (word (candidate i)) a b) := by
 obtain ⟨p,i,hi⟩ := host_to_exact600_reordering_free (restoredColoring f) (restored_good f hc)
  (restored_spokes f) (restored_foreign_one f) (restored_foreign_two f)
 refine ⟨p,i,?_⟩
 intro a b hab
 have hh := hi a b hab
 change (threeIndex (c (physical f (freeLift p a.castSucc)) (physical f (freeLift p b.castSucc)))).val=_ at hh
 have he : (Fin.castLE (by decide) (threeIndex (c (physical f (freeLift p a.castSucc))
  (physical f (freeLift p b.castSucc)))) : Fin 4)=matrix (word (candidate i)) a b := Fin.ext hh
 have hne : freeLift p a.castSucc≠freeLift p b.castSucc :=
  (freeLift p).injective.ne (by intro h;apply hab;apply Fin.ext;exact congrArg (fun x : Fin 16=>x.val) h)
 have hp := (palette_threeIndex _ (physical_avoids_three f hc _ _ hne)).symm
 rw [he] at hp
 exact hp

#print axioms physical_host_to_exact600
#print axioms reordered_preserves_root_foreign
end PricingC.Rooted555
