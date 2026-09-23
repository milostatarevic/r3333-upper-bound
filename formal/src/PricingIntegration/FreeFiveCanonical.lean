import PricingC.Rooted555Free
import PricingC.PhysicalY
import PricingIntegration.BActualFrame

set_option autoImplicit false
namespace PricingIntegration.FreeFiveCanonical
open Ramsey61 Ramsey61.CEncodingCore PricingC PricingC.Rooted555
open PricingABD.TemplateNormalization PricingIntegration.BActualFrame

theorem model_five_cycle (d : R4333.EdgeColoring (Fin 16) (Fin 3))
    (hd : R4333.NoMonochromaticTriangle d) (root : Fin 16)
    (f : Fin 5 ↪ Fin 16) (hne : ∀ i,f i≠root) (hs : ∀ i,d root (f i)=0) :
    ∃ p : Equiv.Perm (Fin 5),∀ i j,i≠j → d (f (p i)) (f (p j))=canonical0 i j := by
  obtain ⟨t,e,hr,he⟩ := k16_rooted_color_preserving_complete d hd root
  let k : Fin 2 := if t then 1 else 0
  have htype : rootTwisted k=t := by cases t <;> decide
  obtain ⟨p0,hp0⟩ := PricingABD.Rooted455Entrance.factors_through_enumeration
    (neighbor0 k) (fun i => e.symm (f i)) (neighbor0_injective k) (e.symm.injective.comp f.injective) (by
      intro i
      have hn : e.symm (f i)≠rootVertex k := by
        intro hn
        apply hne i
        rw [←e.apply_symm_apply (f i),hn]
        exact hr
      apply neighbor0_complete k _ hn
      rw [htype,←he _ _ hn.symm,Equiv.apply_symm_apply]
      change d (e 15) (f i)=0
      rw [hr]
      exact hs i)
  let p := (canonicalEquiv0 k).trans p0.symm
  refine ⟨p,?_⟩
  intro i j hij
  have hc := he (e.symm (f (p i))) (e.symm (f (p j)))
    (e.symm.injective.ne (f.injective.ne (p.injective.ne hij)))
  simp only [Equiv.apply_symm_apply] at hc
  rw [hc,←htype,hp0,hp0]
  change R4333.k16Template (rootTwisted k) (neighbor0 k (p0 (p0.symm (canonicalEquiv0 k i))))
    (neighbor0 k (p0 (p0.symm (canonicalEquiv0 k j))))=_
  simp only [Equiv.apply_symm_apply]
  exact canonicalPerm0_colors k i j hij

/-- The free five-set of a genuine high marked endpoint can always receive
its native C5 order. Only the existing five physical vertices are reordered. -/
theorem actual_free_five_cycle (c : Host) (hc : NoMonochromaticTriangle c)
    (mark root : Vertex) (hm : 15≤colorDegree c (palette 3) mark)
    (hr : root∈colorNeighborhood c (palette 3) mark)
    (f : Fin 5 ↪ Vertex)
    (hf : ∀ i,f i∈colorNeighborhood c (palette 0) root)
    (hg : ∀ i,f i∈colorNeighborhood c (palette 3) mark) :
    ∃ p : Equiv.Perm (Fin 5),∀ i j,i≠j →
      c (f (p i)) (f (p j))=palette (foreign 3 (canonical0 i j)) := by
  classical
  obtain ⟨m⟩ := high_neighborhood_completion c hc mark (palette 3) hm (foreignEquiv 3)
  let r := m.scopeEquiv.symm ⟨root,hr⟩
  have hrv : m.vertex r=root := m.scopeEquiv_symm_val _
  let points := liftPhysical m f hg
  have hpv : ∀ i,m.vertex (points i)=f i := liftPhysical_val m f hg
  let ff : Fin 5 ↪ Fin 16 := ⟨fun i => (points i).val,fun i j h => points.injective (Subtype.ext h)⟩
  have hne : ∀ i,ff i≠r.val := by
    intro i he
    have hp : points i=r := Subtype.ext he
    have hv : f i=root := by rw [←hpv i,hp,hrv]
    exact ((mem_colorNeighborhood _ _ _ _).mp (hf i)).1 hv
  have hsp : ∀ i,m.model r.val (ff i)=0 := by
    intro i
    have hn : r≠points i := by intro he;apply hne i;exact (congrArg Subtype.val he).symm
    have hm' := m.map_color r (points i) hn
    rw [hrv,hpv] at hm'
    have hs := ((mem_colorNeighborhood _ _ _ _).mp (hf i)).2
    apply (foreignEquiv 3).injective
    apply Subtype.ext
    exact hm'.symm.trans hs
  obtain ⟨p,hp⟩ := model_five_cycle m.model m.good r.val ff hne hsp
  refine ⟨p,?_⟩
  intro i j hij
  have hm' := m.map_color (points (p i)) (points (p j)) (points.injective.ne (p.injective.ne hij))
  rw [hpv,hpv] at hm'
  change c (f (p i)) (f (p j))=palette (foreign 3 (m.model (ff (p i)) (ff (p j)))) at hm'
  rw [hp i j hij] at hm'
  exact hm'

#print axioms actual_free_five_cycle
end PricingIntegration.FreeFiveCanonical
