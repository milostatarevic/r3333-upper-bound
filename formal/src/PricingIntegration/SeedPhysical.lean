import PricingIntegration.SeedBindingCore
import PricingIntegration.PhysicalGluing

namespace PricingIntegration.SeedBinding
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
open Ramsey61.CConcreteFamily Ramsey61.CPhysicalNormalization
open PricingG.Completion72

def domain (m : Metadata) : Finset Vertex :=
  Finset.univ.filter fun v => ∃ s a, m.maps s a = some v

def physicalS (m : Metadata) : Finset Vertex := Finset.univ.filter (InS m)

theorem map_mem_domain (m : Metadata) {s : Fin 3} {a : Fin 16} {v : Vertex}
    (h : m.maps s a = some v) : v ∈ domain m :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,s,a,h⟩

theorem physicalS_subset_domain (m : Metadata) : physicalS m ⊆ domain m := by
  intro v hv
  obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hv).2
  exact map_mem_domain m ha

/-- Compatible maps on actual overlapping physical scopes. The fields ask
only for local edge identities, injectivity, fixed root colors and exact
marked-neighborhood image; no global permutation or seed-cover conclusion is
assumed. -/
structure PartialGeometry (c : Host) (m : Metadata) where
  map : {v // v ∈ domain m} → Vertex
  injective : Function.Injective map
  tags : ∀ v, physicalTag (map v) = physicalTag v.val
  template : ∀ s a b u v (hu : m.maps s a = some u) (hv : m.maps s b = some v),
    u ≠ v → c (map ⟨u,map_mem_domain m hu⟩) (map ⟨v,map_mem_domain m hv⟩) =
      palette (scopePalette s (referenceColor (m.states s) a b))
  into : ∀ s (hs : s ∈ physicalS m),
    map ⟨s,physicalS_subset_domain m hs⟩ ∈ colorNeighborhood c (palette 2) 33
  onto : ∀ t ∈ colorNeighborhood c (palette 2) 33,
    ∃ s, ∃ hs : s ∈ physicalS m, map ⟨s,physicalS_subset_domain m hs⟩ = t

/-- A compatible local construction supplies a single whole-host relabeling
and the exact geometry consumed by every stored seed assertion. -/
theorem partial_geometry_gives_geometry (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (hroot : RootConditions c)
    (hmarked : 15 ≤ colorDegree c (palette 2) 33)
    (m : Metadata) (g : PartialGeometry c m) :
    ∃ e : Vertex ≃ Vertex,
      (∀ v : {v // v ∈ domain m}, e v.val = g.map v) ∧
      Geometry (relabel c e (Equiv.refl _)) m ∧
      DenseCounter.FormulaSat (baseValuation (relabel c e (Equiv.refl _))) broaderBaseCNF := by
  obtain ⟨e,he,hgood,hsel,hr,hm,hS,hedges,hbase⟩ :=
    physical_partial_map_supplies_base c hc selectors hroot hmarked
      (domain m) (physicalS m) (physicalS_subset_domain m)
      g.map g.injective g.tags g.into g.onto
  refine ⟨e,he,⟨hr,?_,?_⟩,hbase⟩
  · intro s a b u v hu hv hne
    rw [hedges ⟨u,map_mem_domain m hu⟩ ⟨v,map_mem_domain m hv⟩]
    exact g.template s a b u v hu hv hne
  · intro v
    rw [hS]
    simp [physicalS]

#print axioms partial_geometry_gives_geometry
end PricingIntegration.SeedBinding
