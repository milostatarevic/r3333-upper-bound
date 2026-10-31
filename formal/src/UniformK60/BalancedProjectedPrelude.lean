import UniformK60.BalancedProjectedData

set_option autoImplicit false
namespace UniformK60.BalancedProjectedFinite
open CompletionC.NativeMatrices UniformK60.BalancedProjectedData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Full16-coordinate actions, not merely support permutations. -/
theorem fullAction_bijective : ∀ a, Function.Bijective (fullAction a) := by decide +kernel

theorem fullAction_preserves : ∀ a u v, u≠v →
    R4333.k16Template (actionKind a) (fullAction a u) (fullAction a v)=
      R4333.k16Template (actionKind a) u v := by decide +kernel

theorem geometry_dimensions : ∀ g,
    (geometryShape g).left=5 ∧ (geometryShape g).dimension≤15 ∧
    ((geometryShape g).right=4 ∨ (geometryShape g).right=5) := by decide

theorem row_dimensions : ∀ r,
    (rowShape r).left=5 ∧ (rowShape r).dimension≤15 ∧
    ((rowShape r).right=4 ∨ (rowShape r).right=5) := by decide

theorem geometry_free_le : ∀ g, (geometryShape g).free≤5 := by decide

def realIndex (g : Geometry) (j : Fin 5) : Fin 15 :=
  ⟨(geometryShape g).free+5+j.val, by
    have hf := geometry_free_le g
    have hj := j.isLt
    omega⟩

def realLocal (g : Geometry) (a : Fin 15) : Fin 5 :=
  ⟨(a.val-((geometryShape g).free+5)) % 5, by omega⟩

/-- The chosen coordinate maps preserve all three physical support groups,
and agree with one full16-coordinate action on the real support. -/
def Structural (g : Geometry) (i : Fin 600) : Prop :=
  rowShape (target g i)=geometryShape g ∧
  rowKind (target g i)=geometryKind g ∧
  actionKind (action g i)=geometryKind g ∧
  (∀ a, inverse g i (forward g i a)=a) ∧
  (∀ a, forward g i (inverse g i a)=a) ∧
  (∀ a, group (geometryShape g) (forward g i a)=group (geometryShape g) a) ∧
  (∀ j : Fin 5, j.val<(geometryShape g).right →
    fullAction (action g i) (geometryRealOrder g j)=
      rowRealSupport (target g i) (realLocal g (forward g i (realIndex g j)))) ∧
  (∀ j : Fin 5, j.val<(geometryShape g).right →
    fullAction (action g i)
      (geometryRealOrder g (realLocal g (inverse g i (realIndex g j))))=
        rowRealSupport (target g i) j)

instance (g : Geometry) (i : Fin 600) : Decidable (Structural g i) := by unfold Structural; infer_instance

/-- Every active off-diagonal native entry agrees after transport with the
retained projected row. Internal edges are included in this equality. -/
def MatrixTransport (g : Geometry) (i : Fin 600) : Prop :=
  ∀ a b : Fin (geometryShape g).dimension, a≠b →
    matrix (geometryShape g) (candidate (geometryShape g) i) a b=
      rowMatrix (target g i)
        (forward g i (Fin.castLE (geometry_dimensions g).2.1 a))
        (forward g i (Fin.castLE (geometry_dimensions g).2.1 b))

instance (g : Geometry) (i : Fin 600) : Decidable (MatrixTransport g i) := by unfold MatrixTransport; infer_instance

def chunkIndex (k : Fin 6) (j : Fin 100) : Fin 600 :=
  ⟨100*k.val+j.val,by have := k.isLt;have := j.isLt;omega⟩

#print axioms fullAction_preserves
end UniformK60.BalancedProjectedFinite
