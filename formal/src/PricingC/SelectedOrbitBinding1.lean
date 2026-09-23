import PricingC.NativePairActionData
import PricingC.RemainingOrbit07Data
import PricingC.RemainingOrbit08Data
import PricingC.RemainingOrbit09Data
import PricingC.RemainingOrbit10Data
import PricingC.RemainingOrbit11Data
import PricingC.RemainingOrbit12Data
import PricingC.RemainingOrbit13Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_07 : selectedCodes[7]! = PricingC.RemainingOrbit07.actions := by rfl
theorem selected_coordinate_07 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit07.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨7,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[7]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_07]
 rfl
theorem selected_codes_08 : selectedCodes[8]! = PricingC.RemainingOrbit08.actions := by rfl
theorem selected_coordinate_08 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit08.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨8,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[8]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_08]
 rfl
theorem selected_codes_09 : selectedCodes[9]! = PricingC.RemainingOrbit09.actions := by rfl
theorem selected_coordinate_09 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit09.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨9,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[9]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_09]
 rfl
theorem selected_codes_10 : selectedCodes[10]! = PricingC.RemainingOrbit10.actions := by rfl
theorem selected_coordinate_10 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit10.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨10,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[10]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_10]
 rfl
theorem selected_codes_11 : selectedCodes[11]! = PricingC.RemainingOrbit11.actions := by rfl
theorem selected_coordinate_11 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit11.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨11,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[11]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_11]
 rfl
theorem selected_codes_12 : selectedCodes[12]! = PricingC.RemainingOrbit12.actions := by rfl
theorem selected_coordinate_12 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit12.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨12,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[12]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_12]
 rfl
theorem selected_codes_13 : selectedCodes[13]! = PricingC.RemainingOrbit13.actions := by rfl
theorem selected_coordinate_13 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit13.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨13,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[13]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_13]
 rfl
end PricingC.NativePairActions
