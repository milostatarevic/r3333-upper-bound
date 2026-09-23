import PricingC.Rooted555Lookup
import PricingC.Rooted555Free

namespace PricingC.Rooted555
open R4333

/-- Every actual canonically labelled rooted555 coloring belongs to the exact
600-word native catalogue. All105 physical matrix edges are included. -/
theorem host_to_exact600 (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (h : CanonicalRooted555 c) :
    ∃ i : Fin 600, ∀ a b : Fin 15,a≠b →
      (c a.castSucc b.castSucc).val = (matrix (word (candidate i)) a b).val := by
  obtain ⟨r,e,f,l,u,hr,he,h0,h1,h2⟩ := rooted_isomorphism_cover c hc h
  refine ⟨catalogueIndex r f l u,?_⟩
  have hv (a : Fin 15) : e.symm a.castSucc=chosenVertex r f l u a := by
    unfold chosenVertex
    split_ifs with ha hb
    · rw [show a.castSucc=label0 ⟨a.val,ha⟩ from rfl]
      exact h0 _
    · rw [show a.castSucc=label1 ⟨a.val-5,by omega⟩ from by apply Fin.ext;dsimp [label1];omega]
      exact h1 _
    · rw [show a.castSucc=label2 ⟨a.val-10,by omega⟩ from by apply Fin.ext;dsimp [label2];omega]
      exact h2 _
  intro a b hab
  have hn : e.symm a.castSucc≠e.symm b.castSucc := e.symm.injective.ne (by intro hh;apply hab;apply Fin.ext;exact congrArg (fun x : Fin 16 => x.val) hh)
  have hh := he _ _ hn
  simp only [Equiv.apply_symm_apply] at hh
  rw [hh,hv a,hv b]
  exact all_rooted_choices_in_catalogue r f l u a b hab

theorem host_to_exact600_reordering_free (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c)
    (hs : ∀ i,i≠15 → c 15 i=group i)
    (h1 : ∀ i j,i≠j → c (label1 i) (label1 j)=canonical1 i j)
    (h2 : ∀ i j,i≠j → c (label2 i) (label2 j)=canonical2 i j) :
    ∃ p : Equiv.Perm (Fin 5),∃ i : Fin 600,∀ a b : Fin 15,a≠b →
      (c (freeLift p a.castSucc) (freeLift p b.castSucc)).val =
        (matrix (word (candidate i)) a b).val := by
  obtain ⟨p,hp⟩ := whole_rooted_normalization c hc hs h1 h2
  obtain ⟨i,hi⟩ := host_to_exact600 (relabelFree c p) (relabelFree_good c p hc) hp
  exact ⟨p,i,hi⟩

#print axioms host_to_exact600
#print axioms host_to_exact600_reordering_free
end PricingC.Rooted555
