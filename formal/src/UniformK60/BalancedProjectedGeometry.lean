import UniformK60.BalancedProjectedPrelude
import UniformK60.ClassificationSupportConsumers

set_option autoImplicit false
namespace UniformK60.BalancedProjectedGeometry
open Finset CompletionC.NativeMatrices
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite

def AllowedShape (s : Shape) : Prop := s=.freeFour ∨ s=.rightFour ∨ s=.allFive
instance (s : Shape) : Decidable (AllowedShape s) := by unfold AllowedShape;infer_instance

def representatives (s : Shape) (t : Bool) : List (Finset (Fin 16)) :=
  if (s.right=4) then
    if t then PricingABD.T16SupportCover.representatives4
    else PricingC.U16SupportCover.representatives4
  else if t then PricingABD.T16SupportCover.representatives5
    else PricingC.U16SupportCover.representatives5

theorem real_size_le (g : Geometry) : (geometryShape g).right≤5 := by
  have h := (geometry_dimensions g).2.2
  omega

def realOrder (g : Geometry) : Fin (geometryShape g).right → Fin 16 :=
  fun i => geometryRealOrder g (Fin.castLE (real_size_le g) i)

def geometrySupport (g : Geometry) : Finset (Fin 16) := univ.image (realOrder g)

theorem realOrder_injective : ∀ g, Function.Injective (realOrder g) := by decide

/-- The actual support covers' retained sets are exactly the nine geometries
used by the projected table, including the all-five shape. -/
theorem representative_geometry : ∀ (s : Shape) (t : Bool)
    (i : Fin (representatives s t).length), AllowedShape s →
      ∃ g : Geometry, geometryShape g=s ∧ geometryKind g=t ∧
        geometrySupport g=(representatives s t).get i := by
  decide

theorem admitted_geometry (s : Shape) (hs : AllowedShape s) (t : Bool)
    (support : Finset (Fin 16)) (h : support∈representatives s t) :
    ∃ g : Geometry, geometryShape g=s ∧ geometryKind g=t ∧ geometrySupport g=support := by
  obtain ⟨i,hi⟩ := List.get_of_mem h
  obtain ⟨g,hg,hk,hset⟩ := representative_geometry s t i hs
  exact ⟨g,hg,hk,hset.trans hi⟩

/-- The canonical order includes every real support vertex and realizes the
complete colored path or pentagon in the palette used by the native frame. -/
theorem realOrder_edges : ∀ (g : Geometry) (i j : Fin (geometryShape g).right), i≠j →
    R4333.k16Template (geometryKind g) (realOrder g i) (realOrder g j)=
      if PricingC.Rooted45Orientation.Cycle (geometryShape g).right i.val j.val then 0 else 1 := by
  decide

theorem fakeOrder_injective : Function.Injective fakeOrder := by decide

theorem fakeOrder_edges : ∀ i j : Fin 5, i≠j →
    R4333.k16Template false (fakeOrder i) (fakeOrder j)=
      if PricingC.Rooted45Orientation.Cycle 5 i.val j.val then 0 else 1 := by
  decide

#print axioms admitted_geometry
#print axioms realOrder_edges
end UniformK60.BalancedProjectedGeometry
