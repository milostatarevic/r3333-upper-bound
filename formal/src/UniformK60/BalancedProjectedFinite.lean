import UniformK60.BalancedProjectedChunk00
import UniformK60.BalancedProjectedChunk01
import UniformK60.BalancedProjectedChunk02
import UniformK60.BalancedProjectedChunk03
import UniformK60.BalancedProjectedChunk04
import UniformK60.BalancedProjectedChunk05
import UniformK60.BalancedProjectedChunk10
import UniformK60.BalancedProjectedChunk11
import UniformK60.BalancedProjectedChunk12
import UniformK60.BalancedProjectedChunk13
import UniformK60.BalancedProjectedChunk14
import UniformK60.BalancedProjectedChunk15
import UniformK60.BalancedProjectedChunk20
import UniformK60.BalancedProjectedChunk21
import UniformK60.BalancedProjectedChunk22
import UniformK60.BalancedProjectedChunk23
import UniformK60.BalancedProjectedChunk24
import UniformK60.BalancedProjectedChunk25
import UniformK60.BalancedProjectedChunk30
import UniformK60.BalancedProjectedChunk31
import UniformK60.BalancedProjectedChunk32
import UniformK60.BalancedProjectedChunk33
import UniformK60.BalancedProjectedChunk34
import UniformK60.BalancedProjectedChunk35
import UniformK60.BalancedProjectedChunk40
import UniformK60.BalancedProjectedChunk41
import UniformK60.BalancedProjectedChunk42
import UniformK60.BalancedProjectedChunk43
import UniformK60.BalancedProjectedChunk44
import UniformK60.BalancedProjectedChunk45
import UniformK60.BalancedProjectedChunk50
import UniformK60.BalancedProjectedChunk51
import UniformK60.BalancedProjectedChunk52
import UniformK60.BalancedProjectedChunk53
import UniformK60.BalancedProjectedChunk54
import UniformK60.BalancedProjectedChunk55
import UniformK60.BalancedProjectedChunk60
import UniformK60.BalancedProjectedChunk61
import UniformK60.BalancedProjectedChunk62
import UniformK60.BalancedProjectedChunk63
import UniformK60.BalancedProjectedChunk64
import UniformK60.BalancedProjectedChunk65
import UniformK60.BalancedProjectedChunk70
import UniformK60.BalancedProjectedChunk71
import UniformK60.BalancedProjectedChunk72
import UniformK60.BalancedProjectedChunk73
import UniformK60.BalancedProjectedChunk74
import UniformK60.BalancedProjectedChunk75
import UniformK60.BalancedProjectedChunk80
import UniformK60.BalancedProjectedChunk81
import UniformK60.BalancedProjectedChunk82
import UniformK60.BalancedProjectedChunk83
import UniformK60.BalancedProjectedChunk84
import UniformK60.BalancedProjectedChunk85

set_option autoImplicit false
namespace UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedData

theorem combined_chunk (g : Geometry) (k : Fin 6) (j : Fin 100) :
    Structural g (chunkIndex k j) ∧ MatrixTransport g (chunkIndex k j) := by
  fin_cases g <;> fin_cases k
  · exact chunk_0_0 j
  · exact chunk_0_1 j
  · exact chunk_0_2 j
  · exact chunk_0_3 j
  · exact chunk_0_4 j
  · exact chunk_0_5 j
  · exact chunk_1_0 j
  · exact chunk_1_1 j
  · exact chunk_1_2 j
  · exact chunk_1_3 j
  · exact chunk_1_4 j
  · exact chunk_1_5 j
  · exact chunk_2_0 j
  · exact chunk_2_1 j
  · exact chunk_2_2 j
  · exact chunk_2_3 j
  · exact chunk_2_4 j
  · exact chunk_2_5 j
  · exact chunk_3_0 j
  · exact chunk_3_1 j
  · exact chunk_3_2 j
  · exact chunk_3_3 j
  · exact chunk_3_4 j
  · exact chunk_3_5 j
  · exact chunk_4_0 j
  · exact chunk_4_1 j
  · exact chunk_4_2 j
  · exact chunk_4_3 j
  · exact chunk_4_4 j
  · exact chunk_4_5 j
  · exact chunk_5_0 j
  · exact chunk_5_1 j
  · exact chunk_5_2 j
  · exact chunk_5_3 j
  · exact chunk_5_4 j
  · exact chunk_5_5 j
  · exact chunk_6_0 j
  · exact chunk_6_1 j
  · exact chunk_6_2 j
  · exact chunk_6_3 j
  · exact chunk_6_4 j
  · exact chunk_6_5 j
  · exact chunk_7_0 j
  · exact chunk_7_1 j
  · exact chunk_7_2 j
  · exact chunk_7_3 j
  · exact chunk_7_4 j
  · exact chunk_7_5 j
  · exact chunk_8_0 j
  · exact chunk_8_1 j
  · exact chunk_8_2 j
  · exact chunk_8_3 j
  · exact chunk_8_4 j
  · exact chunk_8_5 j

theorem combined (g : Geometry) (i : Fin 600) : Structural g i ∧ MatrixTransport g i := by
  let k : Fin 6 := ⟨i.val/100, by have := i.isLt;omega⟩
  let j : Fin 100 := ⟨i.val%100,Nat.mod_lt _ (by decide)⟩
  have he : chunkIndex k j=i := by
    apply Fin.ext
    change 100*(i.val/100)+i.val%100=i.val
    omega
  simpa only [he] using combined_chunk g k j

theorem structural (g : Geometry) (i : Fin 600) : Structural g i := (combined g i).1

theorem matrix_transport (g : Geometry) (i : Fin 600) : MatrixTransport g i := (combined g i).2

noncomputable def coordinateEquiv (g : Geometry) (i : Fin 600) : Fin 15 ≃ Fin 15 where
  toFun := forward g i
  invFun := inverse g i
  left_inv := (structural g i).2.2.2.1
  right_inv := (structural g i).2.2.2.2.1

noncomputable def realEquiv (g : Geometry) (i : Fin 600) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (fullAction (action g i)) (fullAction_bijective _)

/-- Pulling a row support coordinate back uses the inverse of the same
whole-template automorphism certified on all120 template edges. -/
theorem inverse_real_coordinates (g : Geometry) (i : Fin 600) (j : Fin 5)
    (hj : j.val<(geometryShape g).right) :
    (realEquiv g i).symm (rowRealSupport (target g i) j)=
      geometryRealOrder g (realLocal g (inverse g i (realIndex g j))) := by
  apply (realEquiv g i).injective
  rw [Equiv.apply_symm_apply]
  exact ((structural g i).2.2.2.2.2.2.2 j hj).symm

#print axioms structural
#print axioms matrix_transport
end UniformK60.BalancedProjectedFinite
