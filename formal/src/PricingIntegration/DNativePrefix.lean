import PricingIntegration.DNativeMaps
import PricingIntegration.DFrameBaseFive

set_option autoImplicit false
namespace PricingIntegration.DNativePrefix
open Ramsey61 Ramsey61.DenseCounter
open Ramsey61.CEncodingCore (palette)
open PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.DFrameColoring PricingIntegration.DFrameRows
open PricingIntegration.NativePrimaryCore

def fourFormula (t : Types) : CNF :=
  NativeRenaming.formula DNativeMaps.fourEncode (R4333.ProfileDFourRowCNF.fmla (kind t))
def fiveFormula (t : Types) : CNF :=
  NativeRenaming.formula DNativeMaps.fiveEncode
    (R4333.ProfileDHighOwnFiveSupportC5Formula.fmla (kind t) 2 (Fin.last 15))

noncomputable def fourValuation {c : Host} (f : Frame c (layout false)) : Valuation :=
  NativeRenaming.valuation (R4333.FiniteColorCNF.coloringValuation (coloring f)) DNativeMaps.fourDecode
noncomputable def fiveValuation {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) : Valuation :=
  NativeRenaming.valuation (DFrameBaseFive.valuation f t hg hc) DNativeMaps.fiveDecode

theorem four_satisfied {c : Host} (f : Frame c (layout false))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    FormulaSat (fourValuation f) (fourFormula t) :=
  NativeRenaming.formula_satisfied _ _ _ DNativeMaps.four_roundtrip _ (four_base_satisfied f t hg hc)

theorem five_satisfied {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    FormulaSat (fiveValuation f t hg hc) (fiveFormula t) :=
  NativeRenaming.formula_satisfied _ _ _ DNativeMaps.five_roundtrip _ (DFrameBaseFive.five_base_satisfied f t hg hc)

theorem four_ordered_edge {c : Host} (f : Frame c (layout false))
    (u v : Fin 50) (q : Fin 4) (huv : u<v) :
    fourValuation f (orderedEdgeVar u v q)=true ↔ c (f.vertex u) (f.vertex v)=palette q := by
  classical
  simp only [fourValuation,NativeRenaming.valuation,decide_eq_true_eq,DNativeMaps.four_decode_ordered u v q huv]
  rw [R4333.FiniteColorCNF.coloringValuation_edgeAtom]
  exact Equiv.symm_apply_eq paletteEquiv

theorem five_ordered_edge {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c)
    (u v : Fin 51) (q : Fin 4) (huv : u<v) :
    fiveValuation f t hg hc (orderedEdgeVar u v q)=true ↔ c (f.vertex u) (f.vertex v)=palette q := by
  classical
  simp only [fiveValuation,NativeRenaming.valuation,decide_eq_true_eq,DNativeMaps.five_decode_ordered u v q huv]
  exact DFrameBaseFive.valuation_edge f t hg hc u v q

theorem four_edge {c : Host} (f : Frame c (layout false))
    (u v : Fin 50) (q : Fin 4) (hne : u≠v) :
    fourValuation f (edgeVar u v q)=true ↔ c (f.vertex u) (f.vertex v)=palette q := by
  unfold edgeVar
  split_ifs with h
  · exact four_ordered_edge f u v q h
  · rw [four_ordered_edge f v u q (lt_of_le_of_ne (le_of_not_gt h) hne.symm),c.color_symm (f.vertex v) (f.vertex u)]

theorem five_edge {c : Host} (f : Frame c (layout true))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c)
    (u v : Fin 51) (q : Fin 4) (hne : u≠v) :
    fiveValuation f t hg hc (edgeVar u v q)=true ↔ c (f.vertex u) (f.vertex v)=palette q := by
  unfold edgeVar
  split_ifs with h
  · exact five_ordered_edge f t hg hc u v q h
  · rw [five_ordered_edge f t hg hc v u q (lt_of_le_of_ne (le_of_not_gt h) hne.symm),c.color_symm (f.vertex v) (f.vertex u)]

#print axioms four_satisfied
#print axioms five_satisfied
#print axioms four_edge
#print axioms five_edge
end PricingIntegration.DNativePrefix
