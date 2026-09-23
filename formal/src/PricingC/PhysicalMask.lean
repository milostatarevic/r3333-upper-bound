import PricingC.ScopeLift
import PricingIntegration.IndependentFive

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore

/-- The physical 2-or-5 law for a full actual independent anchor inside any
actual high neighborhood. The completion's possible missing point is never
counted as a physical vertex. -/
theorem completed_physical_mask (c : Host) (owner : Vertex) (omitted : FourColor)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted})
    (m : CompletedScope c owner omitted palette) (q : Fin 3)
    (A : Finset Vertex) (hA : A.card = 5)
    (hsub : A ⊆ colorNeighborhood c omitted owner)
    (hind : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → c u v ≠ (palette q).val)
    (y : Vertex) (hy : y ∈ colorNeighborhood c omitted owner) (hout : y ∉ A) :
    (A.filter (fun a => c a y = (palette q).val)).card = 2 ∨
    (A.filter (fun a => c a y = (palette q).val)).card = 5 := by
  classical
  let ord := finiteFiveOrder A hA
  let phys : Fin 5 ↪ Vertex := ord.toEmbedding.trans (Function.Embedding.subtype _)
  have hphys : ∀ i, phys i ∈ colorNeighborhood c omitted owner :=
    fun i => hsub (ord i).property
  let a := liftPhysicalAnchor m phys hphys
  let yi := m.scopeEquiv.symm ⟨y,hy⟩
  have hv : ∀ i, m.vertex (a i) = (ord i).val := fun i => liftPhysicalAnchor_val m phys hphys i
  have hyi : m.vertex yi = y := m.scopeEquiv_symm_val ⟨y,hy⟩
  have hia : R4333.IsColorIndependentSet m.model q (referenceAnchor m a) := by
    apply referenceAnchor_independent m a q
    intro i j hij
    rw [hv i,hv j]
    exact hind _ (ord i).property _ (ord j).property
      (fun h => hij (ord.injective (Subtype.ext h)))
  obtain ⟨r,hr,_⟩ := PricingIntegration.IndependentFive.good_K16_independent_five_unique_center
    m.model m.good q (referenceAnchor m a) (referenceAnchor_card m a) hia
  have hao : ∀ i, a i ≠ yi := by
    intro i heq
    have heq' := congrArg m.vertex heq
    rw [hv i,hyi] at heq'
    exact hout (heq' ▸ (ord i).property)
  have hm := ordered_physical_mask m a q yi hao r hr
  have hc : (univ.filter (fun i => c (m.vertex (a i)) (m.vertex yi) = (palette q).val)).card =
      (A.filter (fun a => c a y = (palette q).val)).card := by
    simp only [hv,hyi]
    exact five_filter_card A hA (fun z => c z y = (palette q).val)
  rwa [hc] at hm

/-- Host-valid mask law, with the completion and its catalogue proof fully
constructed from the actual high degree. -/
theorem high_neighborhood_physical_mask (c : Host) (hc : NoMonochromaticTriangle c)
    (owner : Vertex) (omitted : FourColor) (hhigh : 15 ≤ colorDegree c omitted owner)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) (q : Fin 3)
    (A : Finset Vertex) (hA : A.card = 5)
    (hsub : A ⊆ colorNeighborhood c omitted owner)
    (hind : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → c u v ≠ (palette q).val)
    (y : Vertex) (hy : y ∈ colorNeighborhood c omitted owner) (hout : y ∉ A) :
    (A.filter (fun a => c a y = (palette q).val)).card = 2 ∨
    (A.filter (fun a => c a y = (palette q).val)).card = 5 := by
  obtain ⟨m⟩ := high_neighborhood_completion c hc owner omitted hhigh palette
  exact completed_physical_mask c owner omitted palette m q A hA hsub hind y hy hout

#print axioms high_neighborhood_physical_mask
#print axioms completed_physical_mask
end PricingC
