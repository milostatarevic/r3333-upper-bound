import PricingIntegration.DFrameDegrees
import R4333Lean.ProfileDHighOwnFiveSupportC5Formula

set_option autoImplicit false
namespace PricingIntegration.DFrameBaseFive
open Ramsey61
open Ramsey61.CEncodingCore (palette)
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry PricingABD.ABPhysicalBounds
open PricingIntegration.DFrameColoring PricingIntegration.DFrameRows PricingIntegration.DFrameDegrees
open R4333.ProfileDTripleJoinReduction

theorem native_cycle : ∀a b : Fin 5,a≠b → freeColor (layout true) a b=
    R4333.ProfileDHighOwnFiveRowSplit61.decodeRemainingColor 2
      (!R4333.ProfileDHighOwnFiveRowSplit61.canonicalCycleWord.coloring a b) := by
  decide +kernel

noncomputable def canonicalBranch {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDHighOwnFiveSupportC5CNF.CanonicalBranch (kind t) 2 (Fin.last 15) where
  toDegreeFlooredFiveExtension:=degreeFloored f t hg hc
  allFiveOwn:=by
    intro a
    change paletteEquiv.symm (c (f.vertex (ABLayout.free (layout true) a)) (f.vertex (mark (layout true))))=3
    apply (Equiv.symm_apply_eq paletteEquiv).mpr
    change c (f.vertex (ABLayout.free (layout true) a)) (f.vertex (mark (layout true)))=palette 3
    rw [c.color_symm]
    exact hg.mark_free a
  insideCanonical:=by
    intro a b hab
    change paletteEquiv.symm (c (f.vertex (ABLayout.free (layout true) a)) (f.vertex (ABLayout.free (layout true) b)))=_
    apply (Equiv.symm_apply_eq paletteEquiv).mpr
    change c (f.vertex (ABLayout.free (layout true) a)) (f.vertex (ABLayout.free (layout true) b))=
      palette (R4333.ProfileDHighOwnFiveRowSplit61.decodeRemainingColor 2
        (!R4333.ProfileDHighOwnFiveRowSplit61.canonicalCycleWord.coloring a b))
    rw [←native_cycle a b hab]
    exact hg.free a b hab
  tailOwnDegreeLower:=by
    change 9≤R4333.colorDegree (tailColoring f) 3 (45 : Fin 46)
    rw [tailDegree_card]
    exact (marked_tail_bounds f t hg hc).1
  tailOwnDegreeUpper:=by
    change R4333.colorDegree (tailColoring f) 3 (45 : Fin 46)≤10
    rw [tailDegree_card]
    exact (marked_tail_bounds f t hg hc).2

noncomputable def valuation {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) : Sat.Valuation :=
  R4333.ProfileDHighOwnFiveSupportC5Formula.finalValuation (canonicalBranch f t hg hc)

theorem five_base_satisfied {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    (valuation f t hg hc).satisfies_fmla
      (R4333.ProfileDHighOwnFiveSupportC5Formula.fmla (kind t) 2 (Fin.last 15)) :=
  R4333.ProfileDHighOwnFiveSupportC5Formula.canonicalBranch_satisfies_fmla (canonicalBranch f t hg hc)

theorem iterated_preserves_atom
    (specs : List R4333.SequentialAtMostManyCNF.CounterSpec) (v : Sat.Valuation) (a : Nat)
    (hout : ∀s∈specs,¬R4333.SequentialAtMostCNF.InSequentialNamespace s.tag a) :
    R4333.SequentialAtMostManyCNF.iteratedSequentialExtension specs v a ↔ v a := by
  induction specs generalizing v with
  | nil=>rfl
  | cons s ss ih=>
    rw [R4333.SequentialAtMostManyCNF.iteratedSequentialExtension_cons]
    exact (ih _ (by intro z hz;exact hout z (List.mem_cons_of_mem _ hz))).trans
      (R4333.SequentialAtMostCNF.sequentialExtension_eq_of_outside s.tag s.inputs v (hout s List.mem_cons_self))

theorem valuation_preserves_edges {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c)
    (u v : Fin 51) (q : Fin 4) :
    valuation f t hg hc (R4333.FiniteColorCNF.edgeAtom u.val v.val q.val) ↔
      R4333.FiniteColorCNF.coloringValuation (coloring f) (R4333.FiniteColorCNF.edgeAtom u.val v.val q.val) := by
  unfold valuation R4333.ProfileDHighOwnFiveSupportC5Formula.finalValuation
  have he := five_total_eq f t hg hc
  change R4333.SequentialAtMostManyCNF.iteratedSequentialExtension
      (R4333.ProfileDHighOwnFiveSupportC5CNF.counterSpecs 2 (Fin.last 15))
      (R4333.FiniteColorCNF.coloringValuation (R4333.ProfileDHighOwnFiveSupportC5CNF.totalColoring (fiveExtension f t hg hc)))
      (R4333.FiniteColorCNF.edgeAtom u.val v.val q.val) ↔ _
  rw [he]
  apply iterated_preserves_atom
  intro spec hs
  simp only [R4333.ProfileDHighOwnFiveSupportC5CNF.counterSpecs,List.mem_map] at hs
  obtain ⟨context,_,rfl⟩:=hs
  exact R4333.OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    (R4333.ProfileDHighOwnFiveSupportC5CNF.namespaceVertex context)
    (R4333.ProfileDHighOwnFiveSupportC5CNF.namespaceColor context)
    (by omega) (by omega)

theorem valuation_edge {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c)
    (u v : Fin 51) (q : Fin 4) :
    valuation f t hg hc (R4333.FiniteColorCNF.edgeAtom u.val v.val q.val) ↔
      c (f.vertex u) (f.vertex v)=palette q := by
  rw [valuation_preserves_edges,R4333.FiniteColorCNF.coloringValuation_edgeAtom]
  exact Equiv.symm_apply_eq paletteEquiv

#print axioms five_base_satisfied
#print axioms valuation_edge
end PricingIntegration.DFrameBaseFive
