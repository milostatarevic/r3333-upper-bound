import UniformK60.ClassificationFiberOrders
import UniformK60.BalancedProjectedGeometry
import UniformK60.HostNormalization

/-! Physical attaching geometry for the mixed C2-root balance branch.
The second low-color support is oriented to be a pentagon; no template is
assigned to its fourteen-vertex root cell. -/
set_option autoImplicit false
namespace UniformK60.BalancedHostBraceGeometry
open Ramsey61 Finset UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationGeometry CompletionC.NativeMatrices

abbrev support (c : Host) (root mark : Vertex) (q : Color) : Finset Vertex :=
  attachingSupport c root (palette 3) mark (palette q)

/-- The three named root cells exhaust the actual marked neighborhood. -/
theorem support_pattern (c : Host) (hc : NoMonochromaticTriangle c)
    (root mark : Vertex) (hm : mark∈colorNeighborhood c (palette 3) root)
    (hh : 15≤colorDegree c (palette 3) mark) :
    ClassificationGeometry.FourFivePattern (support c root mark 0).card (support c root mark 1).card
      (support c root mark 2).card := by
  have hsum := attachingSupport_partition c hc root (palette 3) mark hm
  have he : (univ : Finset FourColor).erase (palette 3)={palette 0,palette 1,palette 2} := by decide
  rw [he] at hsum
  have hs (f : FourColor→Nat) :
      ∑ q∈({palette 0,palette 1,palette 2} : Finset FourColor),f q=
        f (palette 0)+(f (palette 1)+f (palette 2)) := by simp [palette]
  rw [hs] at hsum
  have h0 : (support c root mark 0).card≤5 :=
    BalancedStructure.inter_le_five c hc (palette 3) (palette 0) (by decide) mark root
  have h1 : (support c root mark 1).card≤5 :=
    BalancedStructure.inter_le_five c hc (palette 3) (palette 1) (by decide) mark root
  have h2 : (support c root mark 2).card≤5 :=
    BalancedStructure.inter_le_five c hc (palette 3) (palette 2) (by decide) mark root
  change colorDegree c (palette 3) mark-1=
    (support c root mark 0).card+((support c root mark 1).card+(support c root mark 2).card) at hsum
  unfold ClassificationGeometry.FourFivePattern
  omega

noncomputable def lowSwap : FourColor≃FourColor := Equiv.swap (palette 0) (palette 1)

theorem lowSwap_palette : ∀ q : Color,lowSwap (palette q)=palette ((Equiv.swap 0 1 : Color≃Color) q) := by
  intro q;fin_cases q <;> decide

theorem lowSwap_zero : lowSwap (palette 0)=palette 1 := lowSwap_palette 0
theorem lowSwap_one : lowSwap (palette 1)=palette 0 := lowSwap_palette 1
theorem lowSwap_two : lowSwap (palette 2)=palette 2 := lowSwap_palette 2
theorem lowSwap_three : lowSwap (palette 3)=palette 3 := lowSwap_palette 3

theorem lowSwap_support (c : Host) (root mark : Vertex) (q : Color) :
    support (relabel c (Equiv.refl _) lowSwap) root mark q=
      support c root mark ((Equiv.swap 0 1 : Color≃Color) q) := by
  ext v
  simp only [support,ClassificationGeometry.attachingSupport,mem_inter,mem_colorNeighborhood,relabel,Equiv.refl_apply,
    Equiv.symm_apply_eq,lowSwap_palette,show (Equiv.swap 0 1 : Color≃Color) 3=3 by decide]

/-- At least one low-color support has five vertices. One global low-color
exchange makes it the fake-cell support while preserving both high colors. -/
theorem orient_low (c : Host) (hc : NoMonochromaticTriangle c)
    (root mark : Vertex) (hm : mark∈colorNeighborhood c (palette 3) root)
    (hh : 15≤colorDegree c (palette 3) mark) :
    ∃ σ : FourColor≃FourColor,(σ=Equiv.refl _ ∨ σ=lowSwap) ∧
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧
      mark∈colorNeighborhood d (palette 3) root ∧
      15≤colorDegree d (palette 3) mark ∧ (support d root mark 1).card=5 := by
  have hp := support_pattern c hc root mark hm hh
  by_cases h5 : (support c root mark 1).card=5
  · exact ⟨Equiv.refl _,Or.inl rfl,hc,hm,hh,h5⟩
  · have h0 : (support c root mark 0).card=5 := by unfold ClassificationGeometry.FourFivePattern at hp;omega
    refine ⟨lowSwap,Or.inr rfl,relabel_noMono c hc _ _,?_,?_,?_⟩
    · simpa only [mem_colorNeighborhood,relabel,Equiv.refl_apply,Equiv.symm_apply_eq,
        lowSwap_three] using hm
    · rw [relabel_degree,lowSwap_three]
      exact hh
    · rw [lowSwap_support]
      exact h0

/-- With the fake support fixed at five, only455,554,555 remain. -/
theorem oriented_shape (c : Host) (hc : NoMonochromaticTriangle c)
    (root mark : Vertex) (hm : mark∈colorNeighborhood c (palette 3) root)
    (hh : 15≤colorDegree c (palette 3) mark) (h5 : (support c root mark 1).card=5) :
    ∃ s : Shape,BalancedProjectedGeometry.AllowedShape s ∧
      (support c root mark 0).card=s.free ∧
      (support c root mark 2).card=s.right := by
  have hp := support_pattern c hc root mark hm hh
  rcases hp with h|h|h|h
  · exact ⟨.freeFour,Or.inl rfl,h.1,h.2.2⟩
  · omega
  · exact ⟨.rightFour,Or.inr (Or.inl rfl),h.1,h.2.2⟩
  · exact ⟨.allFive,Or.inr (Or.inr rfl),h.1,h.2.2⟩

#print axioms orient_low
end UniformK60.BalancedHostBraceGeometry
