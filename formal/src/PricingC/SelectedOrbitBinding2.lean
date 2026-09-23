import PricingC.NativePairActionData
import PricingC.RemainingOrbit14Data
import PricingC.RemainingOrbit15Data
import PricingC.RemainingOrbit16Data
import PricingC.RemainingOrbit17Data
import PricingC.RemainingOrbit18Data
import PricingC.RemainingOrbit19Data
import PricingC.RemainingOrbit20Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_14 : selectedCodes[14]! = PricingC.RemainingOrbit14.actions := by rfl
theorem selected_coordinate_14 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit14.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨14,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[14]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_14]
 rfl
theorem selected_codes_15 : selectedCodes[15]! = PricingC.RemainingOrbit15.actions := by rfl
theorem selected_coordinate_15 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit15.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨15,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[15]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_15]
 rfl
theorem selected_codes_16 : selectedCodes[16]! = PricingC.RemainingOrbit16.actions := by rfl
theorem selected_coordinate_16 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit16.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨16,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[16]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_16]
 rfl
theorem selected_codes_17 : selectedCodes[17]! = PricingC.RemainingOrbit17.actions := by rfl
theorem selected_coordinate_17 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit17.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨17,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[17]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_17]
 rfl
theorem selected_codes_18 : selectedCodes[18]! = PricingC.RemainingOrbit18.actions := by rfl
theorem selected_coordinate_18 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit18.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨18,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[18]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_18]
 rfl
theorem selected_codes_19 : selectedCodes[19]! = PricingC.RemainingOrbit19.actions := by rfl
theorem selected_coordinate_19 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit19.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨19,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[19]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_19]
 rfl
theorem selected_codes_20 : selectedCodes[20]! = PricingC.RemainingOrbit20.actions := by rfl
theorem selected_coordinate_20 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit20.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨20,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[20]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_20]
 rfl
end PricingC.NativePairActions
