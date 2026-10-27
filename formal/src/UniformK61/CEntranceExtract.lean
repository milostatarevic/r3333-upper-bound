import UniformK61.CEntranceDefs
import UniformK61.HostNormalization

set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open Ramsey61.CPhysicalNormalization
open PricingIntegration.BActualFrame PricingIntegration.FixedPhysicalNeighborhood

/-- Convert the established high/high/marked/free palette to common
free/left/right/marked colors using one global permutation. -/
def commonPalette : FourColor ≃ FourColor :=
  ((Equiv.swap (palette 0) (palette 1)).trans
    (Equiv.swap (palette 1) (palette 2))).trans (Equiv.swap (palette 2) (palette 3))

@[simp] theorem commonPalette_zero : commonPalette (palette 0) = palette 3 := by decide
@[simp] theorem commonPalette_one : commonPalette (palette 1) = palette 0 := by decide
@[simp] theorem commonPalette_two : commonPalette (palette 2) = palette 1 := by decide
@[simp] theorem commonPalette_three : commonPalette (palette 3) = palette 2 := by decide

/-- A physical C entrance supplies the common-palette interface. The root
and mark remain actual host vertices throughout this global recoloring. -/
theorem actual_entrance (c : Host) (hc : NoMonochromaticTriangle c)
    (witness : CExteriorWitness c) :
    ∃ σ : FourColor ≃ FourColor, let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ Nonempty (Entrance d) := by
  obtain ⟨r,m,hw,_,hm,hnot⟩ := witness
  obtain ⟨hne,hlow,hhigh⟩ := (witness_edge_semantics c r m).mp ⟨hm,hnot⟩
  obtain ⟨σ,hσ,hd⟩ := exists_ordered_palette c hc r hw (c r m) hlow
  let τ := commonPalette.trans σ
  let d := relabel c (Equiv.refl _) τ
  have hmarked : τ (palette 3) = c r m := by
    simpa only [τ,Equiv.trans_apply,commonPalette_three] using hσ
  have degrees : ∀ q : Color, colorDegree d (palette q) r = rootSize q := by
    intro q
    rw [relabel_degree]
    change colorDegree c (σ (commonPalette (palette q))) r = rootSize q
    fin_cases q
    · change colorDegree c (σ (commonPalette (palette 0))) r = 14
      rw [commonPalette_zero]
      simpa using hd 3
    · change colorDegree c (σ (commonPalette (palette 1))) r = 16
      rw [commonPalette_one]
      simpa using hd 0
    · change colorDegree c (σ (commonPalette (palette 2))) r = 16
      rw [commonPalette_two]
      simpa using hd 1
    · change colorDegree c (σ (commonPalette (palette 3))) r = 14
      rw [commonPalette_three]
      simpa using hd 2
  refine ⟨τ,relabel_noMono c hc (Equiv.refl _) τ,⟨⟨r,m,degrees,?_,?_⟩⟩⟩
  · apply (mem_colorNeighborhood _ _ _ _).mpr
    refine ⟨hne,?_⟩
    change τ.symm (c r m) = palette 3
    rw [←hmarked,Equiv.symm_apply_apply]
  · change 15 ≤ colorDegree (relabel c (Equiv.refl _) τ) (palette 3) m
    simpa only [relabel_degree,Equiv.refl_apply,hmarked] using hhigh

theorem support_shape {c : Host} (e : Entrance c) (hc : NoMonochromaticTriangle c) :
    FourFivePattern
      (attachingSupport c e.root (palette 3) e.mark (palette 0)).card
      (attachingSupport c e.root (palette 3) e.mark (palette 1)).card
      (attachingSupport c e.root (palette 3) e.mark (palette 2)).card := by
  have hsum := attachingSupport_partition c hc e.root (palette 3) e.mark e.mark_mem
  have he : (univ : Finset FourColor).erase (palette 3) = {palette 0,palette 1,palette 2} := by decide
  rw [he] at hsum
  have he2 (f : FourColor → Nat) : ∑ p ∈ ({palette 0,palette 1,palette 2} : Finset FourColor), f p =
      f (palette 0) + (f (palette 1) + f (palette 2)) := by simp [palette]
  rw [he2] at hsum
  have h0 := different_color_intersection_le_five c hc (palette 3) (palette 0) (by decide) e.mark e.root
  have h1 := different_color_intersection_le_five c hc (palette 3) (palette 1) (by decide) e.mark e.root
  have h2 := different_color_intersection_le_five c hc (palette 3) (palette 2) (by decide) e.mark e.root
  have high := e.marked_high
  have upper := fourColor_colorDegree_le_sixteen c hc (palette 3) e.mark
  change (attachingSupport c e.root (palette 3) e.mark (palette 0)).card ≤ 5 at h0
  change (attachingSupport c e.root (palette 3) e.mark (palette 1)).card ≤ 5 at h1
  change (attachingSupport c e.root (palette 3) e.mark (palette 2)).card ≤ 5 at h2
  unfold FourFivePattern
  omega

theorem free_four_or_five {c : Host} (e : Entrance c) (hc : NoMonochromaticTriangle c) :
    (attachingSupport c e.root (palette 3) e.mark (palette 0)).card = 4 ∨
    (attachingSupport c e.root (palette 3) e.mark (palette 0)).card = 5 := by
  have h := support_shape e hc
  unfold FourFivePattern at h
  omega

noncomputable def of_cells {c : Host} (e : Entrance c) (five lt rt : Bool)
    (left : PhysicalNeighborhoodMap c e.root (palette 1) (R4333.k16Template lt))
    (right : PhysicalNeighborhoodMap c e.root (palette 2) (R4333.k16Template rt))
    (hl : left.colors = foreignEquiv 1) (hr : right.colors = foreignEquiv 2)
    (hs : (attachingSupport c e.root (palette 3) e.mark (palette 0)).card = freeSize five) :
    Blocks c five lt rt := by
  classical
  let S := attachingSupport c e.root (palette 3) e.mark (palette 0)
  let z : S ≃ Fin (freeSize five) := Fintype.equivFinOfCardEq (by simpa [S] using hs)
  let f : Fin (freeSize five) ↪ Vertex :=
    ⟨fun i => (z.symm i).val,fun i j h => z.symm.injective (Subtype.ext h)⟩
  refine ⟨e,f,left,right,hl,hr,?_,?_,?_⟩
  · intro i
    exact (mem_inter.mp (z.symm i).property).2
  · intro i
    exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp (z.symm i).property).1).2
  · intro v
    constructor
    · intro hv
      refine ⟨z ⟨v,hv⟩,?_⟩
      change (z.symm (z ⟨v,hv⟩)).val = v
      simp
    · rintro ⟨i,rfl⟩
      exact (z.symm i).property

theorem entrance_has_blocks {c : Host} (e : Entrance c) (hc : NoMonochromaticTriangle c) :
    ∃ five lt rt : Bool, Nonempty (Blocks c five lt rt) := by
  obtain ⟨lt,left,hl⟩ := physical_k16_fixed_palette c hc e.root (palette 1) (e.degrees 1) (foreignEquiv 1)
  obtain ⟨rt,right,hr⟩ := physical_k16_fixed_palette c hc e.root (palette 2) (e.degrees 2) (foreignEquiv 2)
  rcases free_four_or_five e hc with hs | hs
  · exact ⟨false,lt,rt,⟨of_cells e false lt rt left right hl hr hs⟩⟩
  · exact ⟨true,lt,rt,⟨of_cells e true lt rt left right hl hr hs⟩⟩

#print axioms actual_entrance
#print axioms support_shape
#print axioms entrance_has_blocks
end UniformK61.CEntrance
