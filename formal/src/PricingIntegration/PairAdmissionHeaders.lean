import PricingIntegration.PairAdmissionData
set_option autoImplicit false
namespace PricingIntegration.PairAdmission
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Every nativeforeignkind is represented: three16/16 A combinations,
four15/16 B combinations, and the two mixed15/15 D combinations.
The two U/U D owners follow their distinct679-leaf recipe. -/
def nativeHeaderKinds : List (Nat × Nat × Nat) :=
 [(0,2,2),(0,2,3),(0,3,3),(1,0,2),(1,0,3),(1,1,2),(1,1,3),(2,0,1),(2,1,1)]
def expectedHeaders : List Row := nativeHeaderKinds.flatMap fun x=>
 (List.finRange 4).map fun stage=>⟨x.1,x.2.1,x.2.2,stage.val⟩
theorem row_header_census : rowData.toList.toFinset=expectedHeaders.toFinset := by decide +kernel
theorem rowData_size : rowData.size=36 := by decide +kernel

theorem native_header_present (family leftKind rightKind : Nat) (stage : Fin 4)
    (hk : (family,leftKind,rightKind)∈nativeHeaderKinds) :
    ∃i : Fin 36,row i=⟨family,leftKind,rightKind,stage.val⟩ := by
  have hm : (⟨family,leftKind,rightKind,stage.val⟩ : Row)∈expectedHeaders :=
    List.mem_flatMap.mpr ⟨_,hk,List.mem_map.mpr ⟨stage,List.mem_finRange _,rfl⟩⟩
  have hn : (⟨family,leftKind,rightKind,stage.val⟩ : Row)∈rowData.toList := by
    apply List.mem_toFinset.mp
    rw [row_header_census]
    exact List.mem_toFinset.mpr hm
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hn
  have hib : i<36 := by simpa only [Array.length_toList,rowData_size] using hi
  refine ⟨⟨i,hib⟩,?_⟩
  change rowData[i]! = _
  have hai : i<rowData.size := by simpa only [rowData_size] using hib
  rw [getElem!_pos rowData i hai]
  simpa only [Array.getElem_toList] using he
#print axioms native_header_present
end PricingIntegration.PairAdmission
