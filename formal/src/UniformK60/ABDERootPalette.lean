import UniformK60.HostNormalization
import PricingIntegration.ABDRootPalette

/-! One actual-host palette ordering for A/B/D/E. The exhaustive arithmetic
check uses degree sum59, not the published K61 sum60. -/
set_option autoImplicit false
namespace UniformK60.ABDERootPalette
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization

def shape (profile : Fin 4) : Color → Nat :=
  (![![11,16,16,16],![12,15,16,16],![13,15,15,16],![14,15,15,15]] :
    Fin 4 → Color → Nat) profile

def mass (profile : Fin 4) : Nat := (![48,47,46,45] : Fin 4 → Nat) profile

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finite_order : ∀ (profile : Fin 4) (a b c d : Fin 6),
    (11+a.val)+(11+b.val)+(11+c.val)+(11+d.val)=59 →
    mass4 (11+a.val) (11+b.val) (11+c.val) (11+d.val)=mass profile →
    ∃ i : Fin 24, ∀ q : Color,
      (![11+a.val,11+b.val,11+c.val,11+d.val] : Color → Nat)
        (PricingIntegration.ABDRootPalette.permMap i q)=shape profile q := by
  decide +kernel

theorem degree_order (profile : Fin 4) (d : Color → Nat) (hb : ∀ q,d q≤16)
    (hs : d 0+d 1+d 2+d 3=59)
    (hm : mass4 (d 0) (d 1) (d 2) (d 3)=mass profile) :
    ∃ e : Color ≃ Color, ∀ q,d (e q)=shape profile q := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  let a : Fin 6 := ⟨d 0-11,by omega⟩
  let b : Fin 6 := ⟨d 1-11,by omega⟩
  let f : Fin 6 := ⟨d 2-11,by omega⟩
  let g : Fin 6 := ⟨d 3-11,by omega⟩
  have ha : 11+a.val=d 0 := by dsimp [a];omega
  have hb' : 11+b.val=d 1 := by dsimp [b];omega
  have hf : 11+f.val=d 2 := by dsimp [f];omega
  have hg : 11+g.val=d 3 := by dsimp [g];omega
  obtain ⟨i,hi⟩ := finite_order profile a b f g
    (by simpa only [ha,hb',hf,hg] using hs)
    (by simpa only [ha,hb',hf,hg] using hm)
  have hd : (![d 0,d 1,d 2,d 3] : Color → Nat)=d := by funext q;fin_cases q <;> rfl
  refine ⟨PricingIntegration.ABDRootPalette.permEquiv i,?_⟩
  intro q
  change d (PricingIntegration.ABDRootPalette.permMap i q)=_
  simpa only [ha,hb',hf,hg,hd] using hi q

noncomputable def paletteEquiv : Color ≃ FourColor := Equiv.ofBijective palette
  ⟨palette_injective,palette_surjective⟩

/-- A supplied A/B/D/E root is ordered by one global color permutation.
Every actual vertex and the incoming ticket count stay fixed. -/
theorem actual_root_ordered (profile : Fin 4) (c : Host)
    (hc : NoMonochromaticTriangle c) (r : Vertex) (hw : W c r=mass profile) :
    ∃ σ : FourColor ≃ FourColor,
      NoMonochromaticTriangle (relabel c (Equiv.refl _) σ) ∧
      (∀ q : Color,colorDegree (relabel c (Equiv.refl _) σ) (palette q) r=shape profile q) ∧
      H (relabel c (Equiv.refl _) σ) r=H c r := by
  let d : Color → Nat := fun q => colorDegree c (palette q) r
  have hs : d 0+d 1+d 2+d 3=59 := by
    simpa [d,palette,FourColor,Fintype.sum_prod_type,Nat.add_assoc] using fourColor_degree_sum c r
  have hm : mass4 (d 0) (d 1) (d 2) (d 3)=mass profile :=
    (W_eq_mass4 c r).symm.trans hw
  obtain ⟨e,he⟩ := degree_order profile d
    (fun q => fourColor_colorDegree_le_sixteen c hc _ _) hs hm
  let σ := paletteEquiv.symm.trans (e.trans paletteEquiv)
  refine ⟨σ,relabel_noMono c hc _ _,?_,relabel_H c _ _ r⟩
  intro q
  rw [relabel_degree]
  have hp : σ (palette q)=palette (e q) := by
    change paletteEquiv (e (paletteEquiv.symm (paletteEquiv q)))=_
    rw [Equiv.symm_apply_apply]
    rfl
  simpa only [hp,Equiv.refl_apply] using he q

#print axioms actual_root_ordered
end UniformK60.ABDERootPalette
