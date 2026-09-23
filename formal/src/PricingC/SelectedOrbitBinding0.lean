import PricingC.NativePairActionData
import PricingC.RemainingOrbit00Data
import PricingC.RemainingOrbit01Data
import PricingC.RemainingOrbit02Data
import PricingC.RemainingOrbit03Data
import PricingC.RemainingOrbit04Data
import PricingC.RemainingOrbit05Data
import PricingC.RemainingOrbit06Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_00 : selectedCodes[0]! = PricingC.RemainingOrbit00.actions := by rfl
theorem selected_coordinate_00 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit00.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨0,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[0]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_00]
 rfl
theorem selected_codes_01 : selectedCodes[1]! = PricingC.RemainingOrbit01.actions := by rfl
theorem selected_coordinate_01 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit01.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨1,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[1]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_01]
 rfl
theorem selected_codes_02 : selectedCodes[2]! = PricingC.RemainingOrbit02.actions := by rfl
theorem selected_coordinate_02 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit02.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨2,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[2]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_02]
 rfl
theorem selected_codes_03 : selectedCodes[3]! = PricingC.RemainingOrbit03.actions := by rfl
theorem selected_coordinate_03 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit03.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨3,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[3]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_03]
 rfl
theorem selected_codes_04 : selectedCodes[4]! = PricingC.RemainingOrbit04.actions := by rfl
theorem selected_coordinate_04 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit04.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨4,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[4]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_04]
 rfl
theorem selected_codes_05 : selectedCodes[5]! = PricingC.RemainingOrbit05.actions := by rfl
theorem selected_coordinate_05 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit05.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨5,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[5]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_05]
 rfl
theorem selected_codes_06 : selectedCodes[6]! = PricingC.RemainingOrbit06.actions := by rfl
theorem selected_coordinate_06 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit06.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨6,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[6]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_06]
 rfl
end PricingC.NativePairActions
