import UniformK61.BalancedEncodingActualLocal
import UniformK61.BalancedAnchorSupportFinite

set_option autoImplicit false
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedVisible UniformK61.BalancedEncodingData
open PricingIntegration.BActualFrame

def guardSet (c : Host) (s : Scope) : Finset (Fin 16) :=
  Finset.univ.filter fun m => c (ownVertex s (center s)) (otherVertex s m)=palette (guardColor s)
def otherCell (s : Scope) : Finset Vertex := if side s=0 then Y else X

theorem mem_otherCell (s : Scope) (v : Vertex) : v ∈ otherCell s ↔ ∃ m,otherVertex s m=v := by
  by_cases hs : side s=0 <;> simp [otherCell,otherVertex,hs,X,Y]

theorem guard_image (c : Host) (s : Scope) :
    (guardSet c s).image (otherVertex s)=colorNeighborhood c (palette (guardColor s)) (ownVertex s (center s)) ∩ otherCell s := by
  ext v
  constructor
  · rintro hv
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hv
    have hm' : c (ownVertex s (center s)) (otherVertex s m)=palette (guardColor s) := by simpa [guardSet] using hm
    exact Finset.mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨(own_other_ne s _ _).symm,hm'⟩,(mem_otherCell s _).mpr ⟨m,rfl⟩⟩
  · intro hv
    obtain ⟨hv,hcell⟩ := Finset.mem_inter.mp hv
    obtain ⟨m,rfl⟩ := (mem_otherCell s _).mp hcell
    exact Finset.mem_image.mpr ⟨m,by simpa [guardSet] using ((mem_colorNeighborhood _ _ _ _).mp hv).2,rfl⟩

theorem guard_card {c : Host} (h : Conditions c) (s : Scope) : (guardSet c s).card=5 := by
  have hi := Finset.card_image_of_injective (guardSet c s) (other_injective s)
  rw [guard_image] at hi
  have hc : (colorNeighborhood c (palette (guardColor s)) (ownVertex s (center s)) ∩ otherCell s).card=5 := by
    by_cases hs : side s=0
    · simpa [guardColor,ownVertex,otherCell,hs] using h.row_five (center s)
    · simpa [guardColor,ownVertex,otherCell,hs] using h.column_five (center s)
  exact hi.symm.trans hc

theorem guard_independent {c : Host} {o : Owner} (hc : NoMonochromaticTriangle c)
    (hn : Normalized c o.left o.right) (s : Scope) : BalancedAnchor.Independent (otherKind o s) (guardSet c s) := by
  intro a ha b hb hab he
  have haa : c (ownVertex s (center s)) (otherVertex s a)=palette (guardColor s) := by simpa [guardSet] using ha
  have hbb : c (ownVertex s (center s)) (otherVertex s b)=palette (guardColor s) := by simpa [guardSet] using hb
  have hedge := other_template hn s a b hab
  change c (otherVertex s a) (otherVertex s b)=palette (foreign (scopeColor s) (R4333.k16Template (otherKind o s) a b)) at hedge
  rw [he,other_zero_color] at hedge
  exact hc _ _ _ ⟨own_other_ne s _ _,own_other_ne s _ _,(other_injective s).ne hab⟩ ⟨haa.trans hbb.symm,hbb.trans hedge.symm⟩

theorem actual_witnesses {c : Host} {o : Owner} (hc : NoMonochromaticTriangle c)
    (hn : Normalized c o.left o.right) (hvis : Conditions c) : Nonempty (Witnesses c o) := by
  classical
  have hs (s : Scope) : ∃ i : Fin 16,support (otherKind o s) i=guardSet c s :=
    BalancedAnchor.support_complete _ _ (guard_card hvis s) (guard_independent hc hn s)
  let p : Scope → Fin 16 := fun s => Classical.choose (hs s)
  refine ⟨⟨p,?_,fun s => Classical.choice (actual_local_witness hn hvis s)⟩⟩
  intro s m
  have hh : support (otherKind o s) (p s)=guardSet c s := Classical.choose_spec (hs s)
  rw [hh]
  simp [guardSet]

/-- A genuine globally balanced good coloring supplies a satisfying valuation
of one of the three complete physical formulas. All finite coordinate and
auxiliary witnesses are constructed; the only remaining premise at the
external endpoint is UNSAT of these exact formulas. -/
theorem actual_uniform_cover (c : Host) (hc : NoMonochromaticTriangle c) (hu : UniformCommonHighPair c) :
    ∃ o : Owner, ∃ w : Valuation, FormulaSat w (formula o) := by
  obtain ⟨d,hd,o,hn,hvis⟩ := actual_three_owner_conditions c hc hu
  obtain ⟨ws⟩ := actual_witnesses hd hn hvis
  obtain ⟨w,hw,_⟩ := host_witness_satisfies d hd o hn ws
  exact ⟨o,w,hw⟩

#print axioms actual_uniform_cover
end UniformK61.BalancedEncoding
