import PricingC.FourAnchorTables
import PricingC.AnchoredScope
import PricingC.UnanchoredReference
import Mathlib.Logic.Equiv.Fintype

namespace PricingC
open Finset R4333 FourAnchorTables AnchorTables

/-- Any specified four distinct neighbors extend to a complete ordered
five-neighborhood, retaining all four specified physical positions. -/
theorem extend_four_neighbors (d : EdgeColoring (Fin 16) (Fin 3))
    (hd : NoMonochromaticTriangle d) (r : Fin 16) (a : Fin 4 ↪ Fin 16)
    (ha : ∀ j, a j ∈ colorNeighborhood d 0 r) :
    ∃ points : Fin 5 ≃ ↥(clebschA (colorGraph d 0) r),
      ∀ j : Fin 4, (points j.castSucc).val = a j := by
  classical
  have hs := k16_colorGraph_isSRG d hd (0 : Fin 3)
  have hcard : Fintype.card ↥(clebschA (colorGraph d 0) r) = 5 := by
    rw [Fintype.card_coe,card_clebschA _ hs]
  let base := (Fintype.equivFinOfCardEq hcard).symm
  let actual (j : Fin 4) : ↥(clebschA (colorGraph d 0) r) :=
    ⟨a j,by simpa only [clebschA,colorGraph_neighborFinset_eq_colorNeighborhood] using ha j⟩
  let g := fun j : Fin 4 => base.symm (actual j)
  have hg : Function.Injective g := by
    intro i j h
    exact a.injective (congrArg Subtype.val (base.symm.injective h))
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair (fun j : Fin 4 => j.castSucc) g
    (fun i j h => Fin.ext (congrArg (fun x : Fin 5 => x.val) h)) hg
  refine ⟨p.trans base,?_⟩
  intro j
  change (base (p j.castSucc)).val = a j
  rw [hp j]
  exact congrArg Subtype.val (base.apply_symm_apply (actual j))

/-- A colored physical P4 lying inside one five-neighborhood is covered by
exactly the retained six star-anchor reference rows. The fifth position is
an actual, distinct K16 vertex, never S's absent formal point. -/
theorem star_four_reference (d : EdgeColoring (Fin 16) (Fin 3))
    (hd : NoMonochromaticTriangle d) (a : Fin 4 ↪ Fin 16)
    (hpath : ∀ j k, j ≠ k → d (a j) (a k) = pathColor j k)
    (hstar : ∃ r, ∀ j, a j ∈ colorNeighborhood d 0 r) :
    ∃ (i : Fin 6) (e : Fin 16 ≃ Fin 16),
      (∀ j, e (starRoles j) = a j) ∧
      (∀ u v, u ≠ v → d (e u) (e v) = PricingG.Completion72.referenceColor (anchoredIndex i) u v) := by
  classical
  obtain ⟨r,hr⟩ := hstar
  obtain ⟨points,hpoints⟩ := extend_four_neighbors d hd r a hr
  obtain ⟨i,e,_,he,hcolor⟩ := ordered_anchor_reference d hd r points
  have heroles : ∀ j, e (starRoles j) = a j := by
    intro j
    exact (he j.castSucc).trans (hpoints j)
  have hstarpath : PathOn i starRoles := by
    intro j k hjk
    have hne : starRoles j ≠ starRoles k := by
      intro h
      exact hjk (Fin.ext (congrArg (fun x : Fin 5 => x.val) (generators_injective h)))
    have hh := hcolor (starRoles j) (starRoles k) hne
    rw [heroles j,heroles k,hpath j k hjk] at hh
    exact hh.symm
  obtain ⟨i',hi'⟩ := (anchored_exhaustive i).mp ((star_path_completes_cycle i).mp hstarpath)
  exact ⟨i',e,heroles,by simpa only [hi'] using hcolor⟩

#print axioms star_four_reference
end PricingC
