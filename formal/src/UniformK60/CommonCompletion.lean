import UniformK60.CommonHost
import UniformK60.ABDEEntrance
import UniformK60.CommonExchange

/-! Complete the marked-cell placement only after all word symmetries.
Its original critical type survives every allowed global color change. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.CommonCompletion
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationAdapter UniformK60.ClassificationMarkedOmission
open UniformK60.ClassificationMarks UniformK60.PhysicalHelpers
open UniformK60.PhysicalTypeTransport UniformK60.ABDERootPalette
open UniformK60.ABDEOwners UniformK60.ABDEEntrance UniformK60.CommonBlocks
open UniformK60.CommonHost
open PricingABD.ABLayout PricingABD.ABGeometry

/-- Recoloring a prescribed critical cell and restoring its physical palette
keeps its U/T type, including when the marked cell has order15. -/
theorem marked_template_recolored {c : Host} {r : Vertex} {profile : Fin 4}
    (a : Cells c r profile) (σ : FourColor ≃ FourColor)
    (h3 : σ (palette 3)=palette 3) :
    ∃ m : PhysicalNeighborhoodMap (relabel c (Equiv.refl _) σ) r (palette 3)
      (model (large profile 2) (a.types 2)),m.colors=foreignEquiv 3 := by
  have old : PhysicalNeighborhoodMap c r (σ (palette 3))
      (model (large profile 2) (a.types 2)) := by
    rw [h3]
    exact a.cell 2
  exact model_repalette _ _ (physical_relabel σ (palette 3) old) (foreignEquiv 3)

def changeRoot {c : Host} {r : Vertex} {t : Bool} {missing : Missing}
    (m : MarkedBlock c r t missing) (s : Vertex) (hs : s=r) : MarkedBlock c s t missing where
  vertex := m.vertex
  mem_neighborhood i := by rw [hs];exact m.mem_neighborhood i
  map_color := m.map_color

theorem marked16_recolored {c : Host} {r : Vertex} {profile : Fin 4}
    (a : Cells c r profile) (hp : profile≠3) (σ : FourColor ≃ FourColor)
    (h3 : σ (palette 3)=palette 3) :
    ∃ m : PhysicalNeighborhoodMap (relabel c (Equiv.refl _) σ) r (palette 3)
      (R4333.k16Template (a.types 2)),m.colors=foreignEquiv 3 := by
  fin_cases profile
  · exact marked_template_recolored a σ h3
  · exact marked_template_recolored a σ h3
  · exact marked_template_recolored a σ h3
  · exact False.elim (hp rfl)

private theorem actualLow_profile_none : ∀ (profile : Fin 4) (five : Bool),
    profile≠3 → shape profile 0=actualLow ⟨layoutProfile profile,five⟩ none := by
  decide

/-- This is an actual marked16 placement, or an exact marked15 placement
with one of the retained3/9missing positions. No good61 host is involved. -/
theorem after_word {c : Host} {r : Vertex} {profile : Fin 4} {five : Bool}
    (a : Cells c r profile)
    (hd : colorDegree c (palette 0) r=shape profile 0)
    (σ : FourColor ≃ FourColor) (h0 : σ (palette 0)=palette 0)
    (h3 : σ (palette 3)=palette 3)
    (b : Blocks (relabel c (Equiv.refl _) σ) ⟨layoutProfile profile,five⟩ (nativeTypes a.types))
    (hr : b.root=r) :
    ∃ missing : Missing,Nonempty (Completion b missing) ∧
      (profile=3 → ∃ k ∈ markRepresentatives (a.types 2),missing=some k) ∧
      (profile≠3 → missing=none) := by
  let d := relabel c (Equiv.refl _) σ
  have hlow : colorDegree d (palette 0) b.root=shape profile 0 := by
    dsimp only [d]
    rw [relabel_degree,h0,hr]
    exact hd
  have hm : b.mark ∈ colorNeighborhood d (palette 3) r := by
    simpa only [hr] using b.mark_mem
  by_cases hp : profile=3
  · subst profile
    obtain ⟨m,hmp⟩ := marked_template_recolored a σ h3
    obtain ⟨k,hk,n,hn,hmark⟩ := physical_marked_omission m b.mark hm
    have hpal : n.colors=foreignEquiv 3 := hn.trans hmp
    let z : MarkedBlock d b.root (nativeTypes a.types).marked (some k) :=
      changeRoot (ofOmitted n hpal) b.root hr
    have hz : z.vertex (markIndex (some k))=b.mark := by
      change n.vertex (survivingIndex k 14)=b.mark
      have he : survivingIndex k 14=markPosition k := by
        apply Subtype.ext
        exact markedPosition_mark (some k)
      rw [he]
      exact hmark
    refine ⟨some k,⟨⟨z,hz,hlow⟩⟩,?_,?_⟩
    · intro _;exact ⟨k,hk,rfl⟩
    · intro h;exact False.elim (h rfl)
  · obtain ⟨old,hold⟩ := marked16_recolored a hp σ h3
    obtain ⟨n,hn,hmark⟩ := k16_remark old b.mark hm
    have hpal : n.colors=foreignEquiv 3 := hn.trans hold
    let z : MarkedBlock d b.root (nativeTypes a.types).marked none :=
      changeRoot (ofFull n hpal) b.root hr
    have hz : z.vertex (markIndex none)=b.mark := hmark
    have hl : colorDegree d (palette 0) b.root=actualLow ⟨layoutProfile profile,five⟩ none :=
      hlow.trans (actualLow_profile_none profile five hp)
    refine ⟨none,⟨⟨z,hz,hl⟩⟩,?_,fun _ => rfl⟩
    intro he
    exact False.elim (hp he)

#print axioms after_word
end UniformK60.CommonCompletion
