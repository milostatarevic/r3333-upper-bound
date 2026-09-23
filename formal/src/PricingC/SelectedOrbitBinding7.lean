import PricingC.NativePairActionData
import PricingC.RemainingOrbit49Data
import PricingC.RemainingOrbit50Data
import PricingC.RemainingOrbit51Data
import PricingC.RemainingOrbit52Data
import PricingC.RemainingOrbit53Data
import PricingC.RemainingOrbit54Data
import PricingC.RemainingOrbit55Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_49 : selectedCodes[49]! = PricingC.RemainingOrbit49.actions := by rfl
theorem selected_coordinate_49 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit49.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨49,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[49]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_49]
 rfl
theorem selected_codes_50 : selectedCodes[50]! = PricingC.RemainingOrbit50.actions := by rfl
theorem selected_coordinate_50 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit50.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨50,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[50]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_50]
 rfl
theorem selected_codes_51 : selectedCodes[51]! = PricingC.RemainingOrbit51.actions := by rfl
theorem selected_coordinate_51 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit51.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨51,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[51]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_51]
 rfl
theorem selected_codes_52 : selectedCodes[52]! = PricingC.RemainingOrbit52.actions := by rfl
theorem selected_coordinate_52 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit52.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨52,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[52]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_52]
 rfl
theorem selected_codes_53 : selectedCodes[53]! = PricingC.RemainingOrbit53.actions := by rfl
theorem selected_coordinate_53 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit53.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨53,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[53]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_53]
 rfl
theorem selected_codes_54 : selectedCodes[54]! = PricingC.RemainingOrbit54.actions := by rfl
theorem selected_coordinate_54 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit54.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨54,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[54]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_54]
 rfl
theorem selected_codes_55 : selectedCodes[55]! = PricingC.RemainingOrbit55.actions := by rfl
theorem selected_coordinate_55 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit55.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨55,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[55]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_55]
 rfl
end PricingC.NativePairActions
