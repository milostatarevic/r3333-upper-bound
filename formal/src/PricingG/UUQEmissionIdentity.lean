import PricingG.UUQExactNative
import PricingG.P15FastUnits
import PricingG.D9StrongFast
import PricingG.D9Root1Fast
import PricingG.D9Root4Fast
import PricingG.D9Root12Fast
import PricingG.D10ArraySuffix
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace PricingG.UUQEmissionIdentity
open R4333
abbrev Leaf := UUQExactNative.Leaf

def d9Units : D9RestrictedSatisfaction.Leaf → Sat.Fmla
  | .inl i => D9StrongFast.units i
  | .inr (.inl i) => D9Root1Fast.units i
  | .inr (.inr (.inl i)) => D9Root4Fast.units i
  | .inr (.inr (.inr i)) => D9Root12Fast.units i

def kind : Bool → ProfileDTripleJoinReduction.Kind | false => .uuu | true => .uut

def emitted (q : Bool) : Leaf → Sat.Fmla
  | .inl i => ProfileDFourRowCNF.fmla (kind q) ++ P15FastUnits.units i
  | .inr (.inl i) => ProfileDHighOwnFiveSupportC5Formula.fmla (kind q) 2 (Fin.last 15) ++ d9Units i
  | .inr (.inr i) => ProfileDHighOwnFiveSupportC5Formula.fmla (kind q) 2 (Fin.last 15) ++ D10ArraySuffix.arraySuffix i

theorem selected_eq : ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition = (Fin.last 15 : Fin 16) := by
  apply Fin.ext
  rfl

attribute [local irreducible] ProfileDFourRowCNF.fmla ProfileDHighOwnFiveSupportC5Formula.fmla

theorem emitted_eq (q : Bool) (i : Leaf) : emitted q i=UUQExactNative.sparse q i := by
  cases q <;> rcases i with i|i|i
  · exact congrArg (fun f=>ProfileDFourRowCNF.fmla .uuu ++ f) (P15FastUnits.units_eq i)
  · rcases i with i|i|i|i
    · exact congrArg (fun f=>ProfileDUUUDegreeNineQuotientFormula61.strongBase ++ f) (D9StrongFast.units_eq i)
    · exact congrArg (fun f=>ContinuationDegreeNineTwistedRoot1QuotientFormula61.strongBase ++ f) (D9Root1Fast.units_eq i)
    · exact congrArg (fun f=>ContinuationDegreeNineTwistedRoot4QuotientFormula61.strongBase ++ f) (D9Root4Fast.units_eq i)
    · exact congrArg (fun f=>ContinuationDegreeNineTwistedRoot12QuotientFormula61.strongBase ++ f) (D9Root12Fast.units_eq i)
  · simpa only [emitted,kind,UUQExactNative.sparse,UUUSelectedSatisfaction.formula,
      ProfileDDegreeTenMatrixLeafDataUUU2P15.formula,ProfileDDegreeTenMatrixCNF.fixedDegreeTenMatrixFmla,List.append_assoc,
      UUTD10Complete.SelectedPosition,selected_eq] using
      congrArg (fun f=>ProfileDHighOwnFiveSupportC5Formula.fmla .uuu 2 (Fin.last 15) ++ f) (D10ArraySuffix.arraySuffix_eq i)
  · exact congrArg (fun f=>ProfileDFourRowCNF.fmla .uut ++ f) (P15FastUnits.units_eq i)
  · rcases i with i|i|i|i
    · exact congrArg (fun f=>UUTD9StrongFormula.strongBase ++ f) (D9StrongFast.units_eq i)
    · exact congrArg (fun f=>UUTD9Root1Formula.strongBase ++ f) (D9Root1Fast.units_eq i)
    · exact congrArg (fun f=>UUTD9Root4Formula.strongBase ++ f) (D9Root4Fast.units_eq i)
    · exact congrArg (fun f=>UUTD9Root12Formula.strongBase ++ f) (D9Root12Fast.units_eq i)
  · simpa only [emitted,kind,UUQExactNative.sparse,UUTSelectedSatisfaction.formula,
      UUTD10Complete.formula,ProfileDDegreeTenMatrixCNF.fixedDegreeTenMatrixFmla,List.append_assoc,
      UUTD10Complete.SelectedPosition,selected_eq] using
      congrArg (fun f=>ProfileDHighOwnFiveSupportC5Formula.fmla .uut 2 (Fin.last 15) ++ f) (D10ArraySuffix.arraySuffix_eq i)

#print axioms emitted_eq
end PricingG.UUQEmissionIdentity
