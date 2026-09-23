import PricingC.ThreeSupportBalanced
namespace PricingC.ThreeSupportFrame
open Ramsey61 Ramsey61.CEncodingCore
open PricingC.Rooted45Orientation (Cycle)

private theorem left_interior545 : ∀i j:Fin 4,
 (if Cycle 4 i.val j.val then (0:Fin 3) else 2)=PricingC.Rooted45Orientation.interior false
 (label1 (nf:=5) (nr:=5) i) (label1 (nf:=5) (nr:=5) j):=by decide
private theorem right_interior545 : ∀i j:Fin 5,
 (if Cycle 5 i.val j.val then (0:Fin 3) else 1)=PricingC.Rooted45Orientation.interior false
 (label2 (nf:=5) (nl:=4) i) (label2 (nf:=5) (nl:=4) j):=by decide

theorem foreign_canonical545 {c:Host} (f:Frame c 5 4 5):
 PricingC.Rooted45Orientation.ForeignCanonical false (restoredColoring f):=by
 refine ⟨restored_root_edges f,?_⟩
 intro a b hab ha hb hz hg
 change a≠rootLabel 5 4 5 at ha
 change b≠rootLabel 5 4 5 at hb
 change group (nf:=5) (nl:=4) (nr:=5) a≠0 at hz
 change group (nf:=5) (nl:=4) (nr:=5) a=group (nf:=5) (nl:=4) (nr:=5) b at hg
 rcases label_cases (nf:=5) (nl:=4) (nr:=5) a with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
 · exact False.elim (ha rfl)
 · exact False.elim (hz (group_free i))
 · rcases label_cases (nf:=5) (nl:=4) (nr:=5) b with rfl|⟨j,rfl⟩|⟨j,rfl⟩|⟨j,rfl⟩
   · exact False.elim (hb rfl)
   · simp only[group_left,group_free] at hg
     exact False.elim (by cases hg)
   · have hij:i≠j:=by intro h;subst j;exact hab rfl
     exact (restored_left_edges f i j hij).trans (left_interior545 i j)
   · simp only[group_left,group_right] at hg
     exact False.elim (by cases hg)
 · rcases label_cases (nf:=5) (nl:=4) (nr:=5) b with rfl|⟨j,rfl⟩|⟨j,rfl⟩|⟨j,rfl⟩
   · exact False.elim (hb rfl)
   · simp only[group_right,group_free] at hg
     exact False.elim (by cases hg)
   · simp only[group_right,group_left] at hg
     exact False.elim (by cases hg)
   · have hij:i≠j:=by intro h;subst j;exact hab rfl
     exact (restored_right_edges f i j hij).trans (right_interior545 i j)

/-- Actual545 support geometry, including the originalcoloredforeignP4,
reaches the exactnative600word family; local455recoding is fully undone. -/
theorem actual_545_to_catalogue {c:Host} (f:Frame c 5 4 5) (hc:NoMonochromaticTriangle c):
 ∃p:Equiv.Perm (Fin 5),∃i:Fin 600,∀a b:Fin 14,a≠b →
 c (physical f (PricingC.OwnFive15.freeLift p a.castSucc))
   (physical f (PricingC.OwnFive15.freeLift p b.castSucc))=
 palette (PricingC.Rooted45Orientation.matrix false
  (PricingC.Rooted45Orientation.word (PricingC.Rooted45Orientation.candidate false i)) a b):=by
 obtain ⟨p,i,hi⟩:=PricingC.Rooted45Orientation.host_to_exact600_reordering_free false
  (restoredColoring f) (restored_good f hc) (foreign_canonical545 f)
 refine ⟨p,i,?_⟩
 intro a b hab
 apply original_palette f hc _ _ ?_ _ (hi a b hab)
 exact (PricingC.OwnFive15.freeLift p).injective.ne
  (by intro h;apply hab;apply Fin.ext;exact congrArg (fun x:Fin 15=>x.val) h)
#print axioms actual_545_to_catalogue

private theorem left_interior554 : ∀i j:Fin 5,
 (if Cycle 5 i.val j.val then (0:Fin 3) else 2)=PricingC.Rooted45Orientation.interior true
 (label1 (nf:=5) (nr:=4) i) (label1 (nf:=5) (nr:=4) j):=by decide
private theorem right_interior554 : ∀i j:Fin 4,
 (if Cycle 4 i.val j.val then (0:Fin 3) else 1)=PricingC.Rooted45Orientation.interior true
 (label2 (nf:=5) (nl:=5) i) (label2 (nf:=5) (nl:=5) j):=by decide

theorem foreign_canonical554 {c:Host} (f:Frame c 5 5 4):
 PricingC.Rooted45Orientation.ForeignCanonical true (restoredColoring f):=by
 refine ⟨restored_root_edges f,?_⟩
 intro a b hab ha hb hz hg
 change a≠rootLabel 5 5 4 at ha
 change b≠rootLabel 5 5 4 at hb
 change group (nf:=5) (nl:=5) (nr:=4) a≠0 at hz
 change group (nf:=5) (nl:=5) (nr:=4) a=group (nf:=5) (nl:=5) (nr:=4) b at hg
 rcases label_cases (nf:=5) (nl:=5) (nr:=4) a with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
 · exact False.elim (ha rfl)
 · exact False.elim (hz (group_free i))
 · rcases label_cases (nf:=5) (nl:=5) (nr:=4) b with rfl|⟨j,rfl⟩|⟨j,rfl⟩|⟨j,rfl⟩
   · exact False.elim (hb rfl)
   · simp only[group_left,group_free] at hg
     exact False.elim (by cases hg)
   · have hij:i≠j:=by intro h;subst j;exact hab rfl
     exact (restored_left_edges f i j hij).trans (left_interior554 i j)
   · simp only[group_left,group_right] at hg
     exact False.elim (by cases hg)
 · rcases label_cases (nf:=5) (nl:=5) (nr:=4) b with rfl|⟨j,rfl⟩|⟨j,rfl⟩|⟨j,rfl⟩
   · exact False.elim (hb rfl)
   · simp only[group_right,group_free] at hg
     exact False.elim (by cases hg)
   · simp only[group_right,group_left] at hg
     exact False.elim (by cases hg)
   · have hij:i≠j:=by intro h;subst j;exact hab rfl
     exact (restored_right_edges f i j hij).trans (right_interior554 i j)

/-- Actual554 support geometry, including the originalcoloredforeignP4,
reaches the exactnative600word family; local455recoding is fully undone. -/
theorem actual_554_to_catalogue {c:Host} (f:Frame c 5 5 4) (hc:NoMonochromaticTriangle c):
 ∃p:Equiv.Perm (Fin 5),∃i:Fin 600,∀a b:Fin 14,a≠b →
 c (physical f (PricingC.OwnFive15.freeLift p a.castSucc))
   (physical f (PricingC.OwnFive15.freeLift p b.castSucc))=
 palette (PricingC.Rooted45Orientation.matrix true
  (PricingC.Rooted45Orientation.word (PricingC.Rooted45Orientation.candidate true i)) a b):=by
 obtain ⟨p,i,hi⟩:=PricingC.Rooted45Orientation.host_to_exact600_reordering_free true
  (restoredColoring f) (restored_good f hc) (foreign_canonical554 f)
 refine ⟨p,i,?_⟩
 intro a b hab
 apply original_palette f hc _ _ ?_ _ (hi a b hab)
 exact (PricingC.OwnFive15.freeLift p).injective.ne
  (by intro h;apply hab;apply Fin.ext;exact congrArg (fun x:Fin 15=>x.val) h)
#print axioms actual_554_to_catalogue

end PricingC.ThreeSupportFrame
