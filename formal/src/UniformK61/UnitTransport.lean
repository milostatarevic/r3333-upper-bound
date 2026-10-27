import UniformK61.Core
import UniformK61.HostNormalization

set_option autoImplicit false
namespace UniformK61.UnitTransport
open Ramsey61 Ramsey61.CEncodingCore

noncomputable def colorEquiv : Color ≃ FourColor :=
  Equiv.ofBijective palette ⟨palette_injective,palette_surjective⟩

/-- Vertex permutation maps target labels to source labels; the color
permutation maps source colors to target colors. -/
noncomputable def transformed (c : Host) (π : Vertex≃Vertex) (σ : Color≃Color) : Host where
  color u v := colorEquiv (σ (colorEquiv.symm (c (π u) (π v))))
  color_symm u v := by rw [c.color_symm]

theorem transformed_good (c : Host) (hc : NoMonochromaticTriangle c)
    (π : Vertex≃Vertex) (σ : Color≃Color) : NoMonochromaticTriangle (transformed c π σ) := by
  intro u v w hd hm
  exact hc _ _ _ ⟨π.injective.ne hd.1,π.injective.ne hd.2.1,π.injective.ne hd.2.2⟩
    ⟨colorEquiv.symm.injective (σ.injective (colorEquiv.injective hm.1)),
     colorEquiv.symm.injective (σ.injective (colorEquiv.injective hm.2))⟩

theorem transformed_color (c : Host) (π : Vertex≃Vertex) (σ : Color≃Color)
    (u v : Vertex) (q : Color) :
    transformed c π σ u v=palette q ↔ c (π u) (π v)=palette (σ.symm q) := by
  change colorEquiv (σ (colorEquiv.symm (c (π u) (π v))))=colorEquiv q ↔
    c (π u) (π v)=colorEquiv (σ.symm q)
  rw [colorEquiv.injective.eq_iff,Equiv.apply_eq_iff_eq_symm_apply,Equiv.symm_apply_eq]

/-- A target fact agrees with a source fact after one simultaneous change
of labels and palette. Edge orientation is immaterial. -/
def Related (π : Vertex≃Vertex) (σ : Color≃Color) (target source : Core.PhysicalUnit) : Prop :=
  source.positive=target.positive ∧ source.q=σ.symm target.q ∧
    ((source.u=π target.u ∧ source.v=π target.v) ∨
     (source.u=π target.v ∧ source.v=π target.u))

instance (π : Vertex≃Vertex) (σ : Color≃Color) (target source : Core.PhysicalUnit) :
    Decidable (Related π σ target source) := by unfold Related;infer_instance

theorem related_matches (c : Host) (π : Vertex≃Vertex) (σ : Color≃Color)
    (target source : Core.PhysicalUnit) (hsource : Core.UnitMatches c source)
    (h : Related π σ target source) : Core.UnitMatches (transformed c π σ) target := by
  obtain ⟨hs,hq,hv⟩ := h
  have hne : target.u≠target.v := by
    intro he
    apply hsource.1
    rcases hv with ⟨h0,h1⟩|⟨h0,h1⟩ <;> rw [h0,h1,he]
  refine ⟨hne,?_⟩
  have he : c (π target.u) (π target.v)=c source.u source.v := by
    rcases hv with ⟨h0,h1⟩|⟨h0,h1⟩
    · rw [h0,h1]
    · rw [h0,h1,c.color_symm]
  have hcolor := transformed_color c π σ target.u target.v target.q
  rw [he,←hq] at hcolor
  have hf := hsource.2
  rw [hs] at hf
  cases hb : target.positive
  · simp only [hb,Bool.false_eq_true,if_false] at hf ⊢
    exact fun hbad => hf (hcolor.mp hbad)
  · simp only [hb,if_true] at hf ⊢
    exact hcolor.mpr hf

/-- The finite bridge condition used by unit-transport tables. -/
def covers (π : Vertex≃Vertex) (σ : Color≃Color)
    (source target : List Core.PhysicalUnit) : Bool :=
  target.all fun u => source.any fun v => decide (Related π σ u v)

theorem covers_matches (c : Host) (π : Vertex≃Vertex) (σ : Color≃Color)
    (source target : List Core.PhysicalUnit) (hs : Core.UnitsMatch c source)
    (h : covers π σ source target=true) : Core.UnitsMatch (transformed c π σ) target := by
  intro u hu
  have hh := List.all_eq_true.mp h u hu
  obtain ⟨v,hv,hrel⟩ := List.any_eq_true.mp hh
  exact related_matches c π σ u v (hs v hv) (of_decide_eq_true hrel)

theorem covers_satisfiable (c : Host) (hc : NoMonochromaticTriangle c)
    (π : Vertex≃Vertex) (σ : Color≃Color) (source target : List Core.PhysicalUnit)
    (hs : Core.UnitsMatch c source) (h : covers π σ source target=true) :
    ∃w : DenseCounter.Valuation,DenseCounter.FormulaSat w (Core.formula target) :=
  ⟨Core.physicalValuation (transformed c π σ),
   Core.coloring_satisfies_formula _ (transformed_good c hc π σ) target
    (covers_matches c π σ source target hs h)⟩

#print axioms covers_satisfiable
end UniformK61.UnitTransport
