import PricingC.NativePairActionData
import PricingC.RemainingOrbit35Data
import PricingC.RemainingOrbit36Data
import PricingC.RemainingOrbit37Data
import PricingC.RemainingOrbit38Data
import PricingC.RemainingOrbit39Data
import PricingC.RemainingOrbit40Data
import PricingC.RemainingOrbit41Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_35 : selectedCodes[35]! = PricingC.RemainingOrbit35.actions := by rfl
theorem selected_coordinate_35 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit35.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨35,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[35]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_35]
 rfl
theorem selected_codes_36 : selectedCodes[36]! = PricingC.RemainingOrbit36.actions := by rfl
theorem selected_coordinate_36 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit36.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨36,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[36]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_36]
 rfl
theorem selected_codes_37 : selectedCodes[37]! = PricingC.RemainingOrbit37.actions := by rfl
theorem selected_coordinate_37 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit37.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨37,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[37]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_37]
 rfl
theorem selected_codes_38 : selectedCodes[38]! = PricingC.RemainingOrbit38.actions := by rfl
theorem selected_coordinate_38 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit38.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨38,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[38]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_38]
 rfl
theorem selected_codes_39 : selectedCodes[39]! = PricingC.RemainingOrbit39.actions := by rfl
theorem selected_coordinate_39 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit39.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨39,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[39]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_39]
 rfl
theorem selected_codes_40 : selectedCodes[40]! = PricingC.RemainingOrbit40.actions := by rfl
theorem selected_coordinate_40 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit40.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨40,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[40]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_40]
 rfl
theorem selected_codes_41 : selectedCodes[41]! = PricingC.RemainingOrbit41.actions := by rfl
theorem selected_coordinate_41 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit41.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨41,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[41]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_41]
 rfl
end PricingC.NativePairActions
