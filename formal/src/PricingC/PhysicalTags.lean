import PricingC.PhysicalY
import PricingIntegration.PhysicalGluing
import PricingIntegration.SeedBindingCore

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
  Ramsey61.CPhysicalNormalization PricingIntegration PricingIntegration.SeedBinding

 theorem paletteX_binding : ∀ q : Fin 3, (paletteX q).val = palette (scopePalette 0 q) := by decide
 theorem paletteS_binding : ∀ q : Fin 3, (paletteS q).val = palette (scopePalette 1 q) := by decide
 theorem paletteY_binding : ∀ q : Fin 3, (paletteY q).val = palette (scopePalette 2 q) := by decide

 theorem physical_tag_from_root_edge (c : Host) (hroot : RootConditions c)
    (v : Vertex) (q : Color) (hv0 : v ≠ 0) (hv33 : v ≠ 33)
    (hcol : c 0 v = palette q) : physicalTag v = (some (palette q),false) := by
  have hv : v ∈ colorNeighborhood c (palette q) 0 := (mem_colorNeighborhood c _ _ _).mpr ⟨hv0,hcol⟩
  rw [normalized_root_neighborhood c hroot q] at hv
  have hh := canonicalCell_blocks q v (List.mem_toFinset.mp hv)
  simp only [physicalTag,hh,hv33,decide_false]

 theorem physical_tag_in_high_cell (c : Host) (hroot : RootConditions c)
    (v : Vertex) (q : Color) (hq : q ≠ 2)
    (hv : v ∈ colorNeighborhood c (palette q) 0) : physicalTag v = (some (palette q),false) := by
  have hm := (mem_colorNeighborhood c _ _ _).mp hv
  have hv33 : v ≠ 33 := by
    intro e
    subst v
    exact hq (palette_injective (hm.2.symm.trans (hroot.1 2 33 (by decide))))
  exact physical_tag_from_root_edge c hroot v q hm.1 hv33 hm.2

 theorem physical_S_tag (c : Host) (hroot : RootConditions c) (state : Fin 72)
    (s : ReferenceScope c 33 (palette 2) paletteS state)
    (h0 : (0 : Fin 16) ∈ s.present) (hr : s.vertex ⟨0,h0⟩ = 0)
    (a : s.present) :
    physicalTag (s.vertex a) = if a.val = 0 then physicalTag 0 else
      (some (palette (scopePalette 1 (PricingG.Completion72.referenceColor state 0 a.val))),false) := by
  by_cases ha : a.val = 0
  · have he : a = ⟨0,h0⟩ := Subtype.ext ha
    simpa only [ha,if_true,he,hr]
  · simp only [ha,if_false]
    have hv0 : s.vertex a ≠ 0 := by
      intro he
      have h := s.vertex.injective (he.trans hr.symm)
      exact ha (congrArg Subtype.val h)
    have hcol := s.map_color ⟨0,h0⟩ a (fun h => ha (congrArg Subtype.val h).symm)
    rw [hr,paletteS_binding] at hcol
    exact physical_tag_from_root_edge c hroot _ _ hv0 (s.point_not_owner a) hcol

#print axioms physical_S_tag
end PricingC
