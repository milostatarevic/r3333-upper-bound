import PricingG.PentagonSign
import PricingG.BoundedColumns
import PricingG.MixedEdgeCount
import PricingG.GraphSRGTransport

namespace PricingG.SignDesign
open Finset Matrix PricingC

def permutedGraph (σ : Equiv.Perm (Fin 16)) : SimpleGraph (Fin 16) := xorGraph.comap σ
instance permutedGraphDecidable (σ : Equiv.Perm (Fin 16)) : DecidableRel (permutedGraph σ).Adj := by
  intro u v
  change Decidable (xorGraph.Adj (σ u) (σ v))
  infer_instance

theorem permutedGraph_adj (σ : Equiv.Perm (Fin 16)) (u v : Fin 16) :
    (permutedGraph σ).Adj u v ↔ xorGraph.Adj (σ u) (σ v) := by
  exact Iff.rfl

theorem permutedGraph_matrix (σ : Equiv.Perm (Fin 16)) :
    (permutedGraph σ).adjMatrix ℤ = permAdj σ := by
  ext u v
  simp [SimpleGraph.adjMatrix_apply,permutedGraph_adj,permAdj,adjacency]

theorem xorGraph_srg : xorGraph.IsSRGWith 16 5 0 2 := by
  letI := R4333.colorGraphDecidableRel R4333.k16Untwisted (0 : Fin 3)
  exact graphIso_srg legacyZeroToXor
    (R4333.k16_colorGraph_isSRG R4333.k16Untwisted R4333.k16Untwisted_good 0)

def permutedGraphIso (σ : Equiv.Perm (Fin 16)) : permutedGraph σ ≃g xorGraph where
  toEquiv := σ
  map_rel_iff' := by intro u v; exact Iff.rfl

theorem permutedGraph_srg (σ : Equiv.Perm (Fin 16)) :
    (permutedGraph σ).IsSRGWith 16 5 0 2 :=
  graphIso_srg (permutedGraphIso σ).symm xorGraph_srg

/-- WB=V-JV on the exact physical common row labeling. -/
theorem overlap_evaluation_matrix (σ : Equiv.Perm (Fin 16)) :
    permRows σ * overlapMatrix σ = signMatrix - permAdj σ * signMatrix := by
  have h := congrArg (fun M : M5 => permRows σ * M) (overlap_matrix_rescale σ)
  rw [Matrix.mul_smul,← Matrix.mul_assoc,permRows_gram] at h
  simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,ones_row_zero,add_zero] at h
  ext y i
  have hi := congrFun (congrFun h y) i
  simp only [Matrix.smul_apply,Matrix.sub_apply] at hi ⊢
  change 4 * _ = 4 * _ - 4 * _ at hi
  omega

theorem overlap_evaluation (σ : Equiv.Perm (Fin 16)) (y : Fin 16) (i : Fin 5) :
    (∑ j, row (σ y) j * overlap σ j i) = row y i -
      ∑ a ∈ (permutedGraph σ).neighborFinset y, row a i := by
  have h := congrFun (congrFun (overlap_evaluation_matrix σ) y) i
  rw [← permutedGraph_matrix] at h
  simp only [Matrix.sub_apply,Matrix.mul_apply,permRows,overlapMatrix,signMatrix,Matrix.of_apply] at h
  simpa [SimpleGraph.adjMatrix_apply,SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter] using h

set_option maxRecDepth 100000 in
theorem star_row_evaluation_properties : ∀ y a : Fin 16, ¬xorGraph.Adj y a →
    (∀ i, row y i + 3 * row a i ≠ 0 ∧ Even (row y i + 3 * row a i) ∧
      |row y i + 3 * row a i| ≤ 4) ∧
    (univ.filter fun i : Fin 5 => |row y i + 3 * row a i| = 4).card =
      if y = a then 5 else 3 := by decide

set_option maxRecDepth 100000 in
theorem pentagon_row_evaluation_properties : ∀ y a : Fin 16,
    ∀ i, Even (row y i - row a i) ∧ |row y i - row a i| ≤ 2 := by decide

#print axioms overlap_evaluation
#print axioms star_row_evaluation_properties
end PricingG.SignDesign
