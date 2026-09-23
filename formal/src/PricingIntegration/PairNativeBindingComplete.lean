import PricingIntegration.PairNativeBindingPart0
import PricingIntegration.PairNativeBindingPart1
import PricingIntegration.PairNativeBindingPart2
import PricingIntegration.PairNativeBindingPart3
import PricingIntegration.PairNativeBindingPart4
import PricingIntegration.PairNativeBindingPart5
import PricingIntegration.PairNativeBindingPart6
import PricingIntegration.PairNativeBindingPart7
set_option autoImplicit false
namespace PricingIntegration.PairAdmission

theorem all_native_bindings (p : Fin 737) : NativeBinding p := by
 have parts : ∀b : Fin 8,∀j : Fin 100,NativeBinding (bindingIndex b j) := by
  intro b
  fin_cases b
  · exact native_binding_part0
  · exact native_binding_part1
  · exact native_binding_part2
  · exact native_binding_part3
  · exact native_binding_part4
  · exact native_binding_part5
  · exact native_binding_part6
  · exact native_binding_part7
 let b : Fin 8 := ⟨p.val/100,by omega⟩
 let j : Fin 100 := ⟨p.val%100,Nat.mod_lt _ (by decide)⟩
 have h : bindingIndex b j=p := by
  apply Fin.ext
  dsimp [bindingIndex,b,j]
  omega
 rw [←h]
 exact parts b j

/-- The complete36-header1045-pair product cover reaches the same737
native indices whose fullsupportorders and whole-blockactions are checked. -/
theorem native_support_product_admitted (i : Fin 36) (a b : Finset Nat)
    (ha : a∈reps (row i).leftKind ((row i).stage==1))
    (hb : b∈reps (row i).rightKind ((row i).stage==2)) :
    ∃p : Fin 737,NativeBinding p ∧
      (retained p=⟨(row i).family,(row i).leftKind,(row i).rightKind,(row i).stage,a,b⟩ ∨
      ((row i).family=2 ∧ (row i).leftKind=1 ∧ (row i).rightKind=1 ∧
       retained p=exchange ⟨(row i).family,(row i).leftKind,(row i).rightKind,(row i).stage,a,b⟩)) := by
 obtain ⟨p,hp⟩ := support_product_admitted i a b ha hb
 exact ⟨p,all_native_bindings p,hp⟩
#print axioms native_support_product_admitted
end PricingIntegration.PairAdmission
