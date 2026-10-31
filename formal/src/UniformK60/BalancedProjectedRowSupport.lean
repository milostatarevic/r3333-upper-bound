import UniformK60.BalancedProjectedPrelude

set_option autoImplicit false
namespace UniformK60.BalancedProjectedRowSupport
open Finset UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite

theorem realSizeLe (r : Row) : (rowShape r).right≤5 := by
  have h := (row_dimensions r).2.2
  omega

def realOrder (r : Row) : Fin (rowShape r).right → Fin 16 :=
  fun j => rowRealSupport r (Fin.castLE (realSizeLe r) j)

theorem realOrder_injective : ∀ r,Function.Injective (realOrder r) := by
  decide +kernel

def support (r : Row) : Finset (Fin 16) := univ.image (realOrder r)

theorem support_card (r : Row) : (support r).card=(rowShape r).right := by
  rw [support,card_image_of_injective _ (realOrder_injective r)]
  simp

#print axioms realOrder_injective
#print axioms support_card
end UniformK60.BalancedProjectedRowSupport
