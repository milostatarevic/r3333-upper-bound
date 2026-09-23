import PricingG.UUQPhysicalCover
import PricingG.D9PhysicalClauseOrder
import PricingG.UUTD9PhysicalOrder
import PricingIntegration.DNativeMaps

set_option autoImplicit false
set_option maxHeartbeats 0
namespace PricingG.UUQExactNative
open R4333
abbrev Leaf := UUUSelectedSatisfaction.Leaf

def sparse : Bool → Leaf → Sat.Fmla
  | false,.inl i => UUUSelectedSatisfaction.formula (.inl i)
  | false,.inr (.inl i) => D9PhysicalClauseOrder.formula i
  | false,.inr (.inr i) => UUUSelectedSatisfaction.formula (.inr (.inr i))
  | true,.inl i => UUTSelectedSatisfaction.formula (.inl i)
  | true,.inr (.inl i) => UUTD9PhysicalOrder.formula i
  | true,.inr (.inr i) => UUTSelectedSatisfaction.formula (.inr (.inr i))

theorem uuu_model (i : Leaf) (v : Sat.Valuation)
    (hv : v.satisfies_fmla (UUUSelectedSatisfaction.formula i)) :
    v.satisfies_fmla (sparse false i) := by
  rcases i with i | i | i
  · exact hv
  · exact D9PhysicalClauseOrder.original_model_physical_order i v hv
  · exact hv

theorem uut_model (i : Leaf) (v : Sat.Valuation)
    (hv : v.satisfies_fmla (UUTSelectedSatisfaction.formula i)) :
    v.satisfies_fmla (sparse true i) := by
  rcases i with i | i | i
  · exact hv
  · exact UUTD9PhysicalOrder.original_model_physical_order i v hv
  · exact hv

def five : Leaf → Bool | .inl _ => false | .inr _ => true

def native (q : Bool) (i : Leaf) : Ramsey61.DenseCounter.CNF :=
  PricingIntegration.NativeRenaming.formula
    (if five i then PricingIntegration.DNativeMaps.fiveEncode else PricingIntegration.DNativeMaps.fourEncode)
    (sparse q i)

theorem native_of_sparse (q : Bool) (i : Leaf) (v : Sat.Valuation)
    (hv : v.satisfies_fmla (sparse q i)) :
    ∃w : Ramsey61.DenseCounter.Valuation, Ramsey61.DenseCounter.FormulaSat w (native q i) := by
  unfold native
  cases h:five i
  · simp only [Bool.false_eq_true,if_false]
    exact ⟨PricingIntegration.NativeRenaming.valuation v PricingIntegration.DNativeMaps.fourDecode,
      PricingIntegration.NativeRenaming.formula_satisfied v
        PricingIntegration.DNativeMaps.fourEncode PricingIntegration.DNativeMaps.fourDecode
        PricingIntegration.DNativeMaps.four_roundtrip (sparse q i) hv⟩
  · simp only [if_true]
    exact ⟨PricingIntegration.NativeRenaming.valuation v PricingIntegration.DNativeMaps.fiveDecode,
      PricingIntegration.NativeRenaming.formula_satisfied v
        PricingIntegration.DNativeMaps.fiveEncode PricingIntegration.DNativeMaps.fiveDecode
        PricingIntegration.DNativeMaps.five_roundtrip (sparse q i) hv⟩

/-- Complete mathematical entrance from one supplied U/U owner to precisely
its original679 native formulas. The only further premise for exclusion is
that these explicit finite formulas have no satisfying assignment. -/
theorem actual_UU_native {c : Ramsey61.Host} {five : Bool} (q : Bool)
    (b : CompletionC.CommonBlocks.Blocks c ⟨.D,five⟩ ⟨false,false,q⟩)
    (hc : Ramsey61.NoMonochromaticTriangle c) :
    ∃i : Leaf,∃w : Ramsey61.DenseCounter.Valuation,Ramsey61.DenseCounter.FormulaSat w (native q i) := by
  cases q
  · obtain ⟨i,v,hv⟩:=UUQPhysicalCover.uuu b hc
    obtain ⟨w,hw⟩:=native_of_sparse false i v (uuu_model i v hv)
    exact ⟨i,w,hw⟩
  · obtain ⟨i,v,hv⟩:=UUQPhysicalCover.uut b hc
    obtain ⟨w,hw⟩:=native_of_sparse true i v (uut_model i v hv)
    exact ⟨i,w,hw⟩

def NativeExclusions : Prop := ∀q:Bool,∀i:Leaf,∀w:Ramsey61.DenseCounter.Valuation,
    ¬Ramsey61.DenseCounter.FormulaSat w (native q i)

theorem actual_UU_excluded (h : NativeExclusions) {c : Ramsey61.Host} {five : Bool} (q : Bool)
    (b : CompletionC.CommonBlocks.Blocks c ⟨.D,five⟩ ⟨false,false,q⟩)
    (hc : Ramsey61.NoMonochromaticTriangle c) : False := by
  obtain ⟨i,w,hw⟩:=actual_UU_native q b hc
  exact h q i w hw

#check actual_UU_native
#print axioms actual_UU_native
#print axioms actual_UU_excluded
end PricingG.UUQExactNative
