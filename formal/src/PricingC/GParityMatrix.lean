import PricingG.MixedEdgeCount
import Mathlib.Data.ZMod.Basic

namespace PricingC.GParity
open Finset Matrix

 theorem clebsch_square_binary (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) :
    K.adjMatrix (ZMod 2) * K.adjMatrix (ZMod 2) = 1 := by
  have h := hK.matrix_eq (α := ZMod 2)
  rw [pow_two] at h
  calc
    K.adjMatrix (ZMod 2) * K.adjMatrix (ZMod 2) =
      5 • (1 : Matrix (Fin 16) (Fin 16) (ZMod 2)) + 2 • Kᶜ.adjMatrix (ZMod 2) := by
        simpa only [zero_smul,add_zero] using h
    _ = 1 := by
      ext i j
      change (5 : Nat) • ((1 : Matrix (Fin 16) (Fin 16) (ZMod 2)) i j) +
        (2 : Nat) • (Kᶜ.adjMatrix (ZMod 2) i j) = (1 : Matrix (Fin 16) (Fin 16) (ZMod 2)) i j
      simp only [nsmul_eq_mul]
      simp only [Matrix.one_apply,SimpleGraph.adjMatrix_apply]
      split_ifs <;> decide

 def parityProduct (K J : SimpleGraph (Fin 16)) [DecidableRel K.Adj] [DecidableRel J.Adj] :
    Matrix (Fin 16) (Fin 16) (ZMod 2) := K.adjMatrix (ZMod 2) * J.adjMatrix (ZMod 2)

 theorem parityProduct_orthogonal (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2) :
    (parityProduct K J)ᵀ * parityProduct K J = 1 ∧
    parityProduct K J * (parityProduct K J)ᵀ = 1 := by
  have hksq := clebsch_square_binary K hK
  have hjsq := clebsch_square_binary J hJ
  simp only [parityProduct,Matrix.transpose_mul,SimpleGraph.transpose_adjMatrix]
  constructor
  · calc
      (J.adjMatrix (ZMod 2) * K.adjMatrix (ZMod 2)) *
          (K.adjMatrix (ZMod 2) * J.adjMatrix (ZMod 2)) =
        J.adjMatrix (ZMod 2) * (K.adjMatrix (ZMod 2) * K.adjMatrix (ZMod 2)) * J.adjMatrix (ZMod 2) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hksq,Matrix.mul_one,hjsq]
  · calc
      (K.adjMatrix (ZMod 2) * J.adjMatrix (ZMod 2)) *
          (J.adjMatrix (ZMod 2) * K.adjMatrix (ZMod 2)) =
        K.adjMatrix (ZMod 2) * (J.adjMatrix (ZMod 2) * J.adjMatrix (ZMod 2)) * K.adjMatrix (ZMod 2) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hjsq,Matrix.mul_one,hksq]

 theorem parityProduct_entry (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (x y : Fin 16) :
    parityProduct K J x y = (((J.neighborFinset y).filter fun a => K.Adj x a).card : ZMod 2) := by
  rw [parityProduct,J.mul_adjMatrix_apply]
  simp [SimpleGraph.adjMatrix_apply,←sum_filter]

 theorem parityProduct_star (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (a y : Fin 16)
    (hstar : J.neighborFinset y = K.neighborFinset a) :
    ∀ x, parityProduct K J x y = (1 : Matrix (Fin 16) (Fin 16) (ZMod 2)) x a := by
  intro x
  have he := parityProduct_entry K J x y
  rw [hstar] at he
  have hk := parityProduct_entry K K x a
  rw [←hk] at he
  simpa only [parityProduct,clebsch_square_binary K hK] using he

#print axioms parityProduct_orthogonal
#print axioms parityProduct_star
end PricingC.GParity
