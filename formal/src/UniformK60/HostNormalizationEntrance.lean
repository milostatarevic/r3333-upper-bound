import UniformK60.HostNormalization
import UniformK60.Entrance
import PricingIntegration.ABDRootPalette

set_option autoImplicit false
namespace UniformK60.CEntranceExtraction
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization

/-- The two possibilities record the low marked-cell size in C1 and the
side of the15-vertex foreign cell in C2. -/
def shape (c1 orientation : Bool) : Color → Nat :=
  if c1 then if orientation then ![14,16,16,13] else ![13,16,16,14]
  else if orientation then ![14,16,15,14] else ![14,15,16,14]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finite_order : ∀ (c1 : Bool) (a b f g : Fin 4) (markColor : Color),
    (13+a.val)+(13+b.val)+(13+f.val)+(13+g.val)=59 →
    mass4 (13+a.val) (13+b.val) (13+f.val) (13+g.val)=(if c1 then 32 else 31) →
    (![13+a.val,13+b.val,13+f.val,13+g.val] : Color → Nat) markColor<15 →
    ∃ i : Fin 24, ∃ orientation : Bool,
      PricingIntegration.ABDRootPalette.permMap i 3=markColor ∧
      ∀ q : Color, (![13+a.val,13+b.val,13+f.val,13+g.val] : Color → Nat)
        (PricingIntegration.ABDRootPalette.permMap i q)=shape c1 orientation q := by
  decide +kernel

theorem degree_order (c1 : Bool) (d : Color → Nat)
    (hb : ∀ q,13≤d q ∧ d q≤16) (hs : d 0+d 1+d 2+d 3=59)
    (hm : mass4 (d 0) (d 1) (d 2) (d 3)=(if c1 then 32 else 31))
    (markColor : Color) (hl : d markColor<15) :
    ∃ e : Color ≃ Color, ∃ orientation : Bool,
      e 3=markColor ∧ ∀ q,d (e q)=shape c1 orientation q := by
  let a : Fin 4 := ⟨d 0-13,by have := hb 0;omega⟩
  let b : Fin 4 := ⟨d 1-13,by have := hb 1;omega⟩
  let f : Fin 4 := ⟨d 2-13,by have := hb 2;omega⟩
  let g : Fin 4 := ⟨d 3-13,by have := hb 3;omega⟩
  have ha : 13+a.val=d 0 := by dsimp [a];have := hb 0;omega
  have hb' : 13+b.val=d 1 := by dsimp [b];have := hb 1;omega
  have hf : 13+f.val=d 2 := by dsimp [f];have := hb 2;omega
  have hg : 13+g.val=d 3 := by dsimp [g];have := hb 3;omega
  have hd : (![d 0,d 1,d 2,d 3] : Color → Nat)=d := by
    funext q;fin_cases q <;> rfl
  obtain ⟨i,o,hi,ho⟩ := finite_order c1 a b f g markColor
    (by simpa only [ha,hb',hf,hg] using hs)
    (by simpa only [ha,hb',hf,hg] using hm)
    (by simpa only [ha,hb',hf,hg,hd] using hl)
  refine ⟨PricingIntegration.ABDRootPalette.permEquiv i,o,hi,?_⟩
  intro q
  change d (PricingIntegration.ABDRootPalette.permMap i q)=_
  simpa only [ha,hb',hf,hg,hd] using ho q

noncomputable def paletteEquiv : Color ≃ FourColor := Equiv.ofBijective palette
  ⟨palette_injective,palette_surjective⟩

/-- Normalize an actual exterior ticket using only one global color
permutation. The root and sender remain the same physical vertices. -/
theorem actual_entrance_ordered (c : Host) (hc : NoMonochromaticTriangle c)
    (root mark : Vertex) (hw : W c root=32 ∨ W c root=31)
    (hin : mark∈Incoming c root) (hout : mark∉Own c root) :
    ∃ c1 orientation : Bool, ∃ σ : FourColor ≃ FourColor,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d root=H c root ∧ W d root=W c root ∧
      W c root=(if c1 then 32 else 31) ∧
      (∀ q : Color,colorDegree d (palette q) root=shape c1 orientation q) ∧
      mark∈colorNeighborhood d (palette 3) root ∧
      15≤colorDegree d (palette 3) mark := by
  obtain ⟨hne,hl,hh⟩ := (witness_edge_semantics c root mark).mp ⟨hin,hout⟩
  obtain ⟨mc,hmc⟩ := palette_surjective (c root mark)
  have hbool : ∃ c1 : Bool,W c root=(if c1 then 32 else 31) := by
    rcases hw with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  obtain ⟨c1,hc1⟩ := hbool
  let d : Color → Nat := fun q => colorDegree c (palette q) root
  have hs : d 0+d 1+d 2+d 3=59 := by
    simpa [d,palette] using fourColor_degree_sum c root
  have hm : mass4 (d 0) (d 1) (d 2) (d 3)=(if c1 then 32 else 31) :=
    (W_eq_mass4 c root).symm.trans hc1
  obtain ⟨e,o,he3,he⟩ := degree_order c1 d
    (fun q => balanced_degree_bounds c hc root hw (palette q)) hs hm mc
    (by simpa only [d,hmc] using hl)
  let σ := paletteEquiv.symm.trans (e.trans paletteEquiv)
  have hσ : ∀ q, σ (palette q)=palette (e q) := by
    intro q
    change paletteEquiv (e (paletteEquiv.symm (paletteEquiv q)))=_
    rw [Equiv.symm_apply_apply]
    rfl
  have hσ3 : σ (palette 3)=c root mark := by rw [hσ,he3,hmc]
  refine ⟨c1,o,σ,relabel_noMono c hc _ _,relabel_H c _ _ _,relabel_W c _ _ _,hc1,?_,?_,?_⟩
  · intro q;rw [relabel_degree,hσ];exact he q
  · apply (mem_colorNeighborhood _ _ _ _).mpr
    refine ⟨hne,?_⟩
    change σ.symm (c root mark)=palette 3
    rw [← hσ3,Equiv.symm_apply_apply]
  · rw [relabel_degree,hσ3]
    exact hh

/-- Every ordinary entrance supplies the exact C entrance profiles and a
high sender, without a ticket-total inequality or reference-host extension. -/
theorem of_entrance_witness (c : Host) (hc : NoMonochromaticTriangle c)
    (hw : CEntranceWitness c) :
    ∃ root mark : Vertex, ∃ c1 orientation : Bool, ∃ σ : FourColor ≃ FourColor,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧
      (∀ q : Color,colorDegree d (palette q) root=shape c1 orientation q) ∧
      mark∈colorNeighborhood d (palette 3) root ∧
      15≤colorDegree d (palette 3) mark := by
  obtain ⟨root,mark,hm,hin,hout⟩ := hw
  obtain ⟨c1,o,σ,hgood,_,_,_,hd,hmark,hhigh⟩ :=
    actual_entrance_ordered c hc root mark hm hin hout
  exact ⟨root,mark,c1,o,σ,hgood,hd,hmark,hhigh⟩

/-- Preserve the selector's eligible-witness interface. -/
theorem of_exterior_witness (c : Host) (hc : NoMonochromaticTriangle c)
    (hw : CExteriorWitness c) :
    ∃ root mark : Vertex, ∃ c1 orientation : Bool, ∃ σ : FourColor ≃ FourColor,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧
      (∀ q : Color,colorDegree d (palette q) root=shape c1 orientation q) ∧
      mark∈colorNeighborhood d (palette 3) root ∧
      15≤colorDegree d (palette 3) mark :=
  of_entrance_witness c hc (exterior_is_entrance c hw)

#print axioms actual_entrance_ordered
#print axioms of_entrance_witness
#print axioms of_exterior_witness
end UniformK60.CEntranceExtraction
