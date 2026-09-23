import PricingC.PhysicalMask
import Ramsey61.GuardedEntrance
import PricingG.SupportSaturation

namespace PricingG
open Finset Ramsey61 Ramsey61.ClassificationAdapter

/-- A complete coordinate view of one actual sixteen-vertex root neighborhood.
It retains the physical vertex embedding and its entire palette map. -/
structure PhysicalBlock (c : Host) (r : Fin 61) (p : FourColor) where
  model : R4333.EdgeColoring (Fin 16) (Fin 3)
  good : R4333.NoMonochromaticTriangle model
  map : PhysicalNeighborhoodMap c r p model

namespace PhysicalBlock
noncomputable def selectedColor {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (q : FourColor) (hq : q ≠ p) : Fin 3 :=
  b.map.colors.symm ⟨q,hq⟩

@[simp] theorem selectedColor_val {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (q : FourColor) (hq : q ≠ p) :
    (b.map.colors (b.selectedColor q hq)).val = q := by simp [selectedColor]

noncomputable def graph {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (q : FourColor) (hq : q ≠ p) : SimpleGraph (Fin 16) :=
  R4333.colorGraph b.model (b.selectedColor q hq)

noncomputable instance graph_decidable {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (q : FourColor) (hq : q ≠ p) : DecidableRel (b.graph q hq).Adj :=
  R4333.colorGraphDecidableRel b.model (b.selectedColor q hq)

theorem graph_srg {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (q : FourColor) (hq : q ≠ p) :
    (b.graph q hq).IsSRGWith 16 5 0 2 :=
  R4333.k16_colorGraph_isSRG b.model b.good (b.selectedColor q hq)

theorem graph_iff {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (q : FourColor) (hq : q ≠ p) (i j : Fin 16) :
    (b.graph q hq).Adj i j ↔ i ≠ j ∧ c (b.map.vertex i) (b.map.vertex j) = q := by
  change (i ≠ j ∧ b.model i j = b.selectedColor q hq) ↔ _
  constructor
  · rintro ⟨hne,he⟩
    exact ⟨hne, by rw [b.map.map_color i j hne,he,b.selectedColor_val]⟩
  · rintro ⟨hne,he⟩
    refine ⟨hne,b.map.colors.injective ?_⟩
    apply Subtype.ext
    simpa only [b.selectedColor_val] using (b.map.map_color i j hne).symm.trans he

theorem physical_filter_card {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (P : Fin 61 → Prop) [DecidablePred P] :
    (univ.filter fun i => P (b.map.vertex i)).card =
      ((colorNeighborhood c p r).filter P).card := by
  have heq : (univ.filter fun i => P (b.map.vertex i)).image b.map.vertex =
      (colorNeighborhood c p r).filter P := by
    ext x
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨b.map.mem_neighborhood i,(mem_filter.mp hi).2⟩
    · intro h
      obtain ⟨i,rfl⟩ := b.map.covers_neighborhood x (mem_filter.mp h).1
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩,rfl⟩
  rw [← heq,card_image_of_injective _ b.map.vertex.injective]

theorem neighbor_image {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (q : FourColor) (hq : q ≠ p) (i : Fin 16) :
    ((b.graph q hq).neighborFinset i).image b.map.vertex =
      colorNeighborhood c p r ∩ colorNeighborhood c q (b.map.vertex i) := by
  classical
  ext x
  constructor
  · intro h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    obtain ⟨hne,hq'⟩ := (b.graph_iff q hq i j).mp ((b.graph q hq).mem_neighborFinset i j |>.mp hj)
    exact mem_inter.mpr ⟨b.map.mem_neighborhood j,
      (mem_colorNeighborhood _ _ _ _).mpr ⟨b.map.vertex.injective.ne hne.symm,hq'⟩⟩
  · intro h
    obtain ⟨j,rfl⟩ := b.map.covers_neighborhood x (mem_inter.mp h).1
    obtain ⟨hne,hq'⟩ := (mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp h).2
    apply mem_image.mpr
    refine ⟨j,(b.graph q hq).mem_neighborFinset i j |>.mpr ?_,rfl⟩
    exact (b.graph_iff q hq i j).mpr ⟨fun he => hne (congrArg b.map.vertex he.symm),hq'⟩

/-- A genuine five-fiber has an intrinsic unique center in the same physical
block. Its existence comes from the checked critical catalogue. -/
theorem cross_fiber_unique_center {c : Host} {r : Fin 61} {p : FourColor}
    (b : PhysicalBlock c r p) (hc : NoMonochromaticTriangle c)
    (q : FourColor) (hq : q ≠ p) (y : Fin 61)
    (hout : y ∉ colorNeighborhood c p r)
    (hcard : (univ.filter fun i => c (b.map.vertex i) y = q).card = 5) :
    ∃! a : Fin 16, ∀ i, (b.graph q hq).Adj a i ↔ c (b.map.vertex i) y = q := by
  classical
  let S := univ.filter fun i => c (b.map.vertex i) y = q
  have hind : R4333.IsColorIndependentSet b.model (b.selectedColor q hq) S := by
    intro i hi j hj hij he
    have hyi : b.map.vertex i ≠ y := by
      intro h; exact hout (h ▸ b.map.mem_neighborhood i)
    have hyj : b.map.vertex j ≠ y := by
      intro h; exact hout (h ▸ b.map.mem_neighborhood j)
    have hcolor : c (b.map.vertex i) (b.map.vertex j) = q := by
      rw [b.map.map_color i j hij,he,b.selectedColor_val]
    exact hc (b.map.vertex i) (b.map.vertex j) y
      ⟨b.map.vertex.injective.ne hij,hyi,hyj⟩
      ⟨hcolor.trans (mem_filter.mp hi).2.symm,
        (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm⟩
  obtain ⟨a,ha,hu⟩ := PricingIntegration.IndependentFive.good_K16_independent_five_unique_center
    b.model b.good (b.selectedColor q hq) S hcard hind
  have hbridge (a : Fin 16) :
      (∀ i, (b.graph q hq).Adj a i ↔ c (b.map.vertex i) y = q) ↔
      S = R4333.colorNeighborhood b.model (b.selectedColor q hq) a := by
    constructor
    · intro h
      ext i
      have hh := h i
      simpa only [S,mem_filter,mem_univ,true_and,R4333.mem_colorNeighborhood,
        graph,R4333.colorGraph,ne_comm] using hh.symm
    · intro h i
      have hh := congrArg (fun T => i ∈ T) h
      have hi := Iff.of_eq hh
      simpa only [S,mem_filter,mem_univ,true_and,R4333.mem_colorNeighborhood,
        graph,R4333.colorGraph,ne_comm] using hi.symm
  exact ⟨a,(hbridge a).mpr ha,fun a' ha' => hu a' ((hbridge a').mp ha')⟩
end PhysicalBlock

/-- Construct a complete physical view without a catalogue hypothesis. -/
theorem exists_physicalBlock (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (p : FourColor) (hd : colorDegree c p r = 16) :
    Nonempty (PhysicalBlock c r p) := by
  obtain ⟨t,ht,⟨m⟩⟩ := physical_neighborhood_k16 c hc r p hd
  exact ⟨⟨t,R4333.k16CriticalCatalogue_complete.1 t ht,m⟩⟩

#print axioms PhysicalBlock.cross_fiber_unique_center
#print axioms exists_physicalBlock
end PricingG
