import PricingC.NativePairActionData
import PricingC.RemainingOrbit42Data
import PricingC.RemainingOrbit43Data
import PricingC.RemainingOrbit44Data
import PricingC.RemainingOrbit45Data
import PricingC.RemainingOrbit46Data
import PricingC.RemainingOrbit47Data
import PricingC.RemainingOrbit48Data
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_codes_42 : selectedCodes[42]! = PricingC.RemainingOrbit42.actions := by rfl
theorem selected_coordinate_42 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit42.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨42,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[42]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_42]
 rfl
theorem selected_codes_43 : selectedCodes[43]! = PricingC.RemainingOrbit43.actions := by rfl
theorem selected_coordinate_43 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit43.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨43,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[43]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_43]
 rfl
theorem selected_codes_44 : selectedCodes[44]! = PricingC.RemainingOrbit44.actions := by rfl
theorem selected_coordinate_44 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit44.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨44,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[44]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_44]
 rfl
theorem selected_codes_45 : selectedCodes[45]! = PricingC.RemainingOrbit45.actions := by rfl
theorem selected_coordinate_45 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit45.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨45,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[45]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_45]
 rfl
theorem selected_codes_46 : selectedCodes[46]! = PricingC.RemainingOrbit46.actions := by rfl
theorem selected_coordinate_46 (i:Fin 600) (a:Fin 14):
 (PricingC.RemainingOrbit46.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨46,by decide⟩ i) a.val)%14 := by
 change _ = ((selectedCodes[46]!)[i.val]! >>> (4*a.val) &&& 15)%14
 rw [selected_codes_46]
 rfl
theorem selected_codes_47 : selectedCodes[47]! = PricingC.RemainingOrbit47.actions := by rfl
theorem selected_coordinate_47 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit47.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨47,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[47]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_47]
 rfl
theorem selected_codes_48 : selectedCodes[48]! = PricingC.RemainingOrbit48.actions := by rfl
theorem selected_coordinate_48 (i:Fin 600) (a:Fin 15):
 (PricingC.RemainingOrbit48.coordinate i a).val =
 (PricingC.NativeBlockActions.digit (selectedCode ⟨48,by decide⟩ i) a.val)%15 := by
 change _ = ((selectedCodes[48]!)[i.val]! >>> (4*a.val) &&& 15)%15
 rw [selected_codes_48]
 rfl
end PricingC.NativePairActions
