import R4333Lean.ClebschUniqueness
import R4333Lean.CriticalTemplateShadowLaws
import R4333Lean.CriticalCatalogues

namespace PricingC
open Finset R4333 SimpleGraph

def generators : Fin 5 → Fin 16 := ![1,2,4,8,15]
def xorGraph : SimpleGraph (Fin 16) where
  Adj u v := u ≠ v ∧ xorIndex16 u v ∈ ({1,2,4,8,15} : Finset (Fin 16))
  symm := ⟨by intro u v h; simpa [xorIndex16,Nat.xor_comm,ne_comm] using h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance xorGraphDecidable : DecidableRel xorGraph.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ xorIndex16 u v ∈ ({1,2,4,8,15} : Finset (Fin 16)))
  infer_instance

def legacyToXorFn : Fin 16 → Fin 16 := ![0,1,6,7,10,11,12,13,2,3,4,5,8,9,14,15]

def legacyToXor : Fin 16 ≃ Fin 16 where
  toFun := legacyToXorFn
  invFun := ![0,1,8,9,10,11,2,3,12,13,4,5,6,7,14,15]
  left_inv := by decide
  right_inv := by decide

def legacyZeroToXor : colorGraph k16Untwisted (0 : Fin 3) ≃g xorGraph where
  toEquiv := legacyToXor
  map_rel_iff' := by decide

noncomputable def modelXorIso : clebschModelGraph (Fin 5) ≃g xorGraph :=
  clebschModelFin16Iso.trans legacyZeroToXor

@[simp] theorem modelXor_root : modelXorIso (Sum.inl ()) = 0 := rfl

@[simp] theorem modelXor_point (i : Fin 5) : modelXorIso (Sum.inr (Sum.inl i)) = generators i := by
  fin_cases i <;> rfl

/-- Any ordering of the actual five neighbors extends to a complete physical
Clebsch graph coordinate map. The root and all five specified images are fixed. -/
noncomputable def anchoredCoordinates {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsSRGWith 16 5 0 2)
    (root : V) (points : Fin 5 ≃ ↥(clebschA G root)) : xorGraph ≃g G :=
  (modelXorIso.symm.trans (clebschModelCongr points)).trans (clebschModelIsoTo G h root)

@[simp] theorem anchoredCoordinates_root {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsSRGWith 16 5 0 2)
    (root : V) (points : Fin 5 ≃ ↥(clebschA G root)) :
    anchoredCoordinates G h root points 0 = root := by
  have hr : modelXorIso.symm 0 = Sum.inl () := by
    apply modelXorIso.injective
    simp
  change clebschDecode G h root ((clebschModelCongr points) (modelXorIso.symm 0)) = root
  rw [hr]
  rfl

@[simp] theorem anchoredCoordinates_point {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsSRGWith 16 5 0 2)
    (root : V) (points : Fin 5 ≃ ↥(clebschA G root)) (i : Fin 5) :
    anchoredCoordinates G h root points (generators i) = (points i).val := by
  have hr : modelXorIso.symm (generators i) = Sum.inr (Sum.inl i) := by
    apply modelXorIso.injective
    simp
  change clebschDecode G h root ((clebschModelCongr points)
    (modelXorIso.symm (generators i))) = (points i).val
  rw [hr]
  rfl

#print axioms anchoredCoordinates
#print axioms anchoredCoordinates_point
end PricingC
