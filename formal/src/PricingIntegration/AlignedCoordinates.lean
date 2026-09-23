import PricingIntegration.ScopeReindex
import PricingC.SelectedTriple

namespace PricingIntegration.SeedBinding
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase Ramsey61.CPhysicalNormalization
open PricingC PricingIntegration.SeedCensus PricingG.Completion72

noncomputable def actualX {c : Host} {b : Boundary} (t : AlignedTriple c b) :
    Present (metadata (index b)) 0 ↪ Vertex where
  toFun a := t.xs.physical.x.vertex ⟨a.val,by rw [t.xs.physical.x_full]; exact Finset.mem_univ _⟩
  inj' := by
    intro a d h
    exact Subtype.ext (congrArg (fun z : t.xs.physical.x.present => z.val) (t.xs.physical.x.vertex.injective h))

theorem sPresent {c : Host} {b : Boundary} (t : AlignedTriple c b)
    (a : Present (metadata (index b)) 1) : a.val ∈ t.xs.physical.s.present :=
  (t.xs.present_match _).mpr ((s_present_exact b a.val).mp a.property)

noncomputable def actualS {c : Host} {b : Boundary} (t : AlignedTriple c b) :
    Present (metadata (index b)) 1 ↪ Vertex where
  toFun a := t.xs.physical.s.vertex ⟨a.val,sPresent t a⟩
  inj' := by
    intro a d h
    exact Subtype.ext (congrArg (fun z : t.xs.physical.s.present => z.val) (t.xs.physical.s.vertex.injective h))

noncomputable def actualY {c : Host} {b : Boundary} (t : AlignedTriple c b) :
    Present (metadata (index b)) 2 ↪ Vertex where
  toFun a := t.y.at a.val
  inj' := by intro a d h; exact Subtype.ext (t.y.at_injective h)

noncomputable def actual {c : Host} {b : Boundary} (t : AlignedTriple c b) :
    (s : Fin 3) → Present (metadata (index b)) s ↪ Vertex
  | 0 => actualX t
  | 1 => actualS t
  | 2 => actualY t

theorem actual_colors {c : Host} {b : Boundary} (t : AlignedTriple c b)
    (s : Fin 3) (a d : Present (metadata (index b)) s) (hne : a ≠ d) :
    c (actual t s a) (actual t s d) =
      palette (scopePalette s (referenceColor ((metadata (index b)).states s) a.val d.val)) := by
  have hn : a.val ≠ d.val := fun h => hne (Subtype.ext h)
  have hs : s = 0 ∨ s = 1 ∨ s = 2 := by fin_cases s <;> simp
  rcases hs with rfl | rfl | rfl
  · have h := t.xs.physical.x.map_color
      ⟨a.val,by rw [t.xs.physical.x_full]; exact Finset.mem_univ _⟩
      ⟨d.val,by rw [t.xs.physical.x_full]; exact Finset.mem_univ _⟩
      (fun e => hn (congrArg (fun z : t.xs.physical.x.present => z.val) e))
    change c (actualX t a) (actualX t d) = _
    rw [(states_exact b).1,t.xs.pair_match]
    exact h.trans (paletteX_binding _)
  · have h := t.xs.physical.s.map_color ⟨a.val,sPresent t a⟩ ⟨d.val,sPresent t d⟩
      (fun e => hn (congrArg (fun z : t.xs.physical.s.present => z.val) e))
    change c (actualS t a) (actualS t d) = _
    rw [(states_exact b).2.1,t.xs.pair_match]
    exact h.trans (paletteS_binding _)
  · have h := t.y.map_color ⟨a.val,by rw [t.y.full]; exact Finset.mem_univ _⟩
      ⟨d.val,by rw [t.y.full]; exact Finset.mem_univ _⟩
      (fun e => hn (congrArg (fun z : t.y.present => z.val) e))
    change c (actualY t a) (actualY t d) = _
    rw [(states_exact b).2.2]
    exact h.trans (paletteY_binding _)

private theorem x_canonical_tag : ∀ a : Fin 16,
    physicalTag (⟨a.val+1,by omega⟩ : Vertex) = (some (palette 0),false) := by decide

private theorem y_canonical_tag : ∀ v : Vertex, 17 ≤ v.val → v.val ≤ 32 →
    physicalTag v = (some (palette 1),false) := by decide

theorem actual_tags {c : Host} {b : Boundary} (t : AlignedTriple c b)
    (hroot : RootConditions c) (s : Fin 3) (a : Present (metadata (index b)) s) :
    physicalTag (actual t s a) = physicalTag (canonical _ _ a) := by
  have hs : s = 0 ∨ s = 1 ∨ s = 2 := by fin_cases s <;> simp
  rcases hs with rfl | rfl | rfl
  · have ht := physical_tag_in_high_cell c hroot (actualX t a) 0 (by decide)
      (t.xs.physical.x.mem_scope ⟨a.val,by rw [t.xs.physical.x_full]; exact Finset.mem_univ _⟩)
    change physicalTag (actualX t a) = _
    rw [ht]
    unfold canonical
    rw [x_map_exact]
    exact (x_canonical_tag a.val).symm
  · have ht := physical_S_tag c hroot _ t.xs.physical.s t.xs.physical.root_present
      t.xs.physical.root_image ⟨a.val,sPresent t a⟩
    have hc := s_physical_tags b a.val a.property
    rw [t.xs.pair_match] at hc
    exact ht.trans hc.symm
  · have ht := physical_tag_in_high_cell c hroot (actualY t a) 1 (by decide)
      (t.y.mem_scope ⟨a.val,by rw [t.y.full]; exact Finset.mem_univ _⟩)
    have hr := (y_map_complete b (canonical _ _ a)).mp ⟨a.val,canonical_some _ _ a⟩
    exact ht.trans (y_canonical_tag _ hr.1 hr.2).symm

theorem actual_xs_agree {c : Host} {b : Boundary} (t : AlignedTriple c b)
    (a : Present (metadata (index b)) 0) (d : Present (metadata (index b)) 1)
    (h : canonical _ _ a = canonical _ _ d) : actualX t a = actualS t d := by
  have he : (metadata (index b)).maps 1 d.val = (metadata (index b)).maps 0 a.val := by
    rw [canonical_some _ _ a,canonical_some _ _ d,h]
  obtain ⟨j,hjS,hjX⟩ := (sx_overlap_exact b d.val a.val).mp he
  have hx : actualX t a = t.xs.physical.anchor j := by
    change t.xs.physical.x.vertex _ = _
    convert t.xs.physical.x_anchor_image j using 1
    exact congrArg t.xs.physical.x.vertex (Subtype.ext hjX)
  have hs : actualS t d = t.xs.physical.anchor j := by
    change t.xs.physical.s.vertex _ = _
    convert t.xs.physical.s_anchor_image j using 1
    exact congrArg t.xs.physical.s.vertex (Subtype.ext hjS)
  exact hx.trans hs.symm

theorem actual_ys_agree {c : Host} {b : Boundary} (t : AlignedTriple c b)
    (a : Present (metadata (index b)) 2) (d : Present (metadata (index b)) 1)
    (h : canonical _ _ a = canonical _ _ d) : actualY t a = actualS t d := by
  have he : (metadata (index b)).maps 1 d.val = (metadata (index b)).maps 2 a.val := by
    rw [canonical_some _ _ a,canonical_some _ _ d,h]
  obtain ⟨j,hj,hjS,hjY⟩ := (sy_overlap_exact b d.val a.val).mp he
  change t.y.at a.val = t.xs.physical.s.vertex _
  rw [hjY,t.agreement j hj]
  exact congrArg t.xs.physical.s.vertex (Subtype.ext hjS.symm)

#print axioms actual_colors
#print axioms actual_xs_agree
end PricingIntegration.SeedBinding
