import PricingC.NativePairActionData
import PricingC.RemainingOrbit28Data
import PricingC.RemainingOrbit29Data
import PricingC.RemainingOrbit30Data
import PricingC.RemainingOrbit31Data
import PricingC.RemainingOrbit32Data
import PricingC.RemainingOrbit33Data
import PricingC.RemainingOrbit34Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_28 : selectedCodes[28]! = PricingC.RemainingOrbit28.actions := by rfl
theorem selected_coordinate_28 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit28.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨28,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[28]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_28]
 rfl
theorem selected_codes_29 : selectedCodes[29]! = PricingC.RemainingOrbit29.actions := by rfl
theorem selected_coordinate_29 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit29.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨29,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[29]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_29]
 rfl
theorem selected_codes_30 : selectedCodes[30]! = PricingC.RemainingOrbit30.actions := by rfl
theorem selected_coordinate_30 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit30.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨30,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[30]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_30]
 rfl
theorem selected_codes_31 : selectedCodes[31]! = PricingC.RemainingOrbit31.actions := by rfl
theorem selected_coordinate_31 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit31.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨31,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[31]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_31]
 rfl
theorem selected_codes_32 : selectedCodes[32]! = PricingC.RemainingOrbit32.actions := by rfl
theorem selected_coordinate_32 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit32.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨32,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[32]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_32]
 rfl
theorem selected_codes_33 : selectedCodes[33]! = PricingC.RemainingOrbit33.actions := by rfl
theorem selected_coordinate_33 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit33.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨33,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[33]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_33]
 rfl
theorem selected_codes_34 : selectedCodes[34]! = PricingC.RemainingOrbit34.actions := by rfl
theorem selected_coordinate_34 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit34.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨34,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[34]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_34]
 rfl
end PricingC.NativePairActions
