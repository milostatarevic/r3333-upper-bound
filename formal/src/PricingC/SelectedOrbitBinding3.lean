import PricingC.NativePairActionData
import PricingC.RemainingOrbit21Data
import PricingC.RemainingOrbit22Data
import PricingC.RemainingOrbit23Data
import PricingC.RemainingOrbit24Data
import PricingC.RemainingOrbit25Data
import PricingC.RemainingOrbit26Data
import PricingC.RemainingOrbit27Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_21 : selectedCodes[21]! = PricingC.RemainingOrbit21.actions := by rfl
theorem selected_coordinate_21 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit21.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨21,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[21]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_21]
 rfl
theorem selected_codes_22 : selectedCodes[22]! = PricingC.RemainingOrbit22.actions := by rfl
theorem selected_coordinate_22 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit22.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨22,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[22]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_22]
 rfl
theorem selected_codes_23 : selectedCodes[23]! = PricingC.RemainingOrbit23.actions := by rfl
theorem selected_coordinate_23 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit23.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨23,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[23]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_23]
 rfl
theorem selected_codes_24 : selectedCodes[24]! = PricingC.RemainingOrbit24.actions := by rfl
theorem selected_coordinate_24 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit24.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨24,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[24]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_24]
 rfl
theorem selected_codes_25 : selectedCodes[25]! = PricingC.RemainingOrbit25.actions := by rfl
theorem selected_coordinate_25 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit25.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨25,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[25]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_25]
 rfl
theorem selected_codes_26 : selectedCodes[26]! = PricingC.RemainingOrbit26.actions := by rfl
theorem selected_coordinate_26 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit26.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨26,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[26]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_26]
 rfl
theorem selected_codes_27 : selectedCodes[27]! = PricingC.RemainingOrbit27.actions := by rfl
theorem selected_coordinate_27 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit27.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨27,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[27]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_27]
 rfl
end PricingC.NativePairActions
