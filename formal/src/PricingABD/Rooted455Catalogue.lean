import PricingABD.Rooted455Entrance
import PricingABD.Rooted455Lookup

namespace PricingABD.Rooted455Catalogue
open R4333 PricingABD.Rooted455Entrance PricingABD.Rooted455Data PricingABD.Rooted455Lookup
open PricingABD.P15PairOrbit PricingABD.P15MatrixTransport

/-- Every good canonically labelled rooted4|5|5coloring belongs to the exact
600-word catalogue. Classification, root choices, support isomorphisms and
allmatrixedges are proved; no catalogue-completeness axiom is assumed. -/
theorem host_to_exact600 (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (h : CanonicalRooted455 c) :
    ∃ i : Fin 600, ∀ a b : Fin 14,a≠b →
      (c a.castSucc b.castSucc).val = (matrix (word (candidate i)) a b).val := by
  obtain ⟨r,e,f,l,u,hr,he,h0,h1,h2⟩ := rooted_isomorphism_cover c hc h
  refine ⟨catalogueIndex r f l u,?_⟩
  have hv (a : Fin 14) : e.symm a.castSucc=chosenVertex r f l u a := by
    unfold chosenVertex
    split_ifs with ha hb
    · rw [show a.castSucc=label0 ⟨a.val,ha⟩ from rfl]
      exact h0 _
    · rw [show a.castSucc=label1 ⟨a.val-4,by omega⟩ from by apply Fin.ext;dsimp [label1];omega]
      exact h1 _
    · rw [show a.castSucc=label2 ⟨a.val-9,by omega⟩ from by apply Fin.ext;dsimp [label2];omega]
      exact h2 _
  intro a b hab
  have hn : e.symm a.castSucc≠e.symm b.castSucc := e.symm.injective.ne (by intro hh;apply hab;apply Fin.ext;exact congrArg (fun x : Fin 15 => x.val) hh)
  have hh := he _ _ hn
  simp only [Equiv.apply_symm_apply] at hh
  rw [hh,hv a,hv b]
  exact all_rooted_choices_in_exact_catalogue r f l u a b hab

#print axioms host_to_exact600
#check host_to_exact600
end PricingABD.Rooted455Catalogue
