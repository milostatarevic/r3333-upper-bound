import PricingABD.ABBase
import PricingABD.ABProgram
import PricingIntegration.NativeClauseBounds

set_option autoImplicit false
namespace PricingABD.ABPrefix
open Ramsey61 Ramsey61.DenseCounter PricingABD.ABLayout PricingABD.ABGeometry PricingABD.ABBase
open PricingABD.ABProgram PricingABD.ABScheduleTypes PricingIntegration.NativePrimaryCore PricingIntegration.NativePrimary
open PricingIntegration.NativeClauseBounds PricingIntegration.ThresholdCompile

theorem base_below (l : Layout) (t : Types) :
    ∀cl∈physicalBase l t,∀x∈cl,x.2<edgeLimit (vertexCount l) := by
  intro cl hcl x hx
  simp only [physicalBase,List.mem_append] at hcl
  rcases hcl with ((((hp|ht)|hfix)|hforbid)|hfree)|hmark
  · exact physicalClauses_bound (vertex_bounds l) cl hp x hx
  · exact triangleClauses_bound (vertex_bounds l) cl ht x hx
  · exact units_below t _ (by intro e he;simp [fixedEdges,he]) cl hfix x hx
  · exact forbidden_below l cl hforbid x hx
  · exact units_below t _ (by intro e he;simp [fixedEdges,he]) cl hfree x hx
  · exact units_below t _ (by intro e he;simp [fixedEdges,he]) cl hmark x hx

def exactPrefix {l : Layout} {M N : Nat} (p : Program l M N) (t : Types) : CNF :=
  physicalBase l t ++ formula p ++ [[(true,high l (mark l))]]

theorem satisfying_extension {c : Host} {l : Layout} {M N : Nat}
    (p : Program l M N) (s t : Types) (hst : SameSchedule l t s)
    (checkedFold : ∀i,FoldOK p s i) (checkedInput : ∀j,InputOK p j)
    (checkedStart : ∀j,p.start j=PricingIntegration.MultiSparseCounter.start (primaryLimit l)
      (PricingIntegration.MultiSparseCounter.size p.inputs p.height) j)
    (f : Frame c l) (hc : NoMonochromaticTriangle c) (hg : Geometry t f) :
    ∃w:Valuation,(∀a<primaryLimit l,w a=primary f a) ∧ FormulaSat w (exactPrefix p t) := by
  obtain ⟨w,hw,hp⟩:=ABProgram.satisfying_extension p s t hst checkedFold checkedInput checkedStart f hc hg
  have hb : FormulaSat w (physicalBase l t) :=
    preserves_prior_formula (primary f) w (primaryLimit l) _ hw
      (by intro cl hcl x hx;have he:=base_below l t cl hcl x hx;unfold primaryLimit;omega)
      (base_sat f hc hg)
  refine ⟨w,hw,?_⟩
  simp only [exactPrefix,formulaSat_append]
  refine ⟨⟨hb,hp⟩,?_⟩
  intro cl hcl
  have he:cl=[(true,high l (mark l))] := by simpa using hcl
  subst cl
  refine ⟨(true,high l (mark l)),by simp,?_⟩
  rw [hw _ (by have hh:=(mark l).isLt;unfold high primaryLimit;omega)]
  exact (primary_high f (mark l)).mpr f.marked_high

#print axioms satisfying_extension
end PricingABD.ABPrefix
