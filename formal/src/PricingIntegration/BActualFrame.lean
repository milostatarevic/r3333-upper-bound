import PricingIntegration.FixedPhysicalNeighborhood
import PricingIntegration.ABDRootPalette
import PricingABD.BPhysicalBounds

set_option autoImplicit false

namespace PricingIntegration.BActualFrame
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open PricingIntegration.FixedPhysicalNeighborhood PricingIntegration.ABDRootPalette

/-- The three other colors, in the exact increasing order used by the native
A/B/D template units. -/
def foreign (omitted : Color) : Fin 3 → Color :=
  (![![1,2,3],![0,2,3],![0,1,3],![0,1,2]] : Color → Fin 3 → Color) omitted

def foreignFn (omitted : Color) (i : Fin 3) : {q : FourColor // q ≠ palette omitted} :=
  ⟨palette (foreign omitted i),by fin_cases omitted <;> fin_cases i <;> decide⟩

private theorem foreignFn_bijective : ∀ omitted,Function.Bijective (foreignFn omitted) := by decide
noncomputable def foreignEquiv (omitted : Color) : Fin 3 ≃ {q : FourColor // q ≠ palette omitted} :=
  Equiv.ofBijective (foreignFn omitted) (foreignFn_bijective omitted)

abbrev Index := Fin 5 ⊕ (Fin 15 ⊕ (Fin 16 ⊕ Fin 16))

def indexEquiv : Index ≃ Fin 52 :=
  (Equiv.sumCongr (Equiv.refl (Fin 5))
    ((Equiv.sumCongr (Equiv.refl (Fin 15)) finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def indexOwner : Index → Color
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

theorem owner_index : ∀ i, PricingABD.BPhysicalBounds.owner (indexEquiv i)=indexOwner i := by decide

theorem indexed_same_block {i j : Index} (h : indexOwner i = indexOwner j) :
    (∃ a b : Fin 5,i=.inl a ∧ j=.inl b) ∨
    (∃ a b : Fin 15,i=.inr (.inl a) ∧ j=.inr (.inl b)) ∨
    (∃ a b : Fin 16,i=.inr (.inr (.inl a)) ∧ j=.inr (.inr (.inl b))) ∨
    (∃ a b : Fin 16,i=.inr (.inr (.inr a)) ∧ j=.inr (.inr (.inr b))) := by
  rcases i with i|i|i|i <;> rcases j with j|j|j|j
  all_goals simp_all [indexOwner]

structure Blocks (c : Host) (r : Vertex) where
  free : Fin 5 ↪ Vertex
  mType : Bool
  xType : Bool
  qType : Bool
  m : PhysicalNeighborhoodMap c r (palette 1) (R4333.k15Template mType)
  x : PhysicalNeighborhoodMap c r (palette 2) (R4333.k16Template xType)
  q : PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template qType)
  free_mem : ∀ i,free i ∈ colorNeighborhood c (palette 0) r
  m_palette : m.colors = foreignEquiv 1
  x_palette : x.colors = foreignEquiv 2
  q_palette : q.colors = foreignEquiv 3
  marked_high : q.vertex 15 ∈ Incoming c r

def Blocks.physical {c : Host} {r : Vertex} (b : Blocks c r) : Index → Vertex
  | .inl i => b.free i
  | .inr (.inl i) => b.m.vertex i
  | .inr (.inr (.inl i)) => b.x.vertex i
  | .inr (.inr (.inr i)) => b.q.vertex i

theorem Blocks.mem {c : Host} {r : Vertex} (b : Blocks c r) (i : Index) :
    b.physical i ∈ colorNeighborhood c (palette (indexOwner i)) r := by
  rcases i with i|i|i|i
  · exact b.free_mem i
  · exact b.m.mem_neighborhood i
  · exact b.x.mem_neighborhood i
  · exact b.q.mem_neighborhood i

theorem Blocks.physical_injective {c : Host} {r : Vertex} (b : Blocks c r) :
    Function.Injective b.physical := by
  intro i j hij
  have ho : indexOwner i = indexOwner j := by
    apply palette_injective
    exact (((mem_colorNeighborhood _ _ _ _).mp (b.mem i)).2.symm.trans
      (congrArg (c r) hij)).trans (((mem_colorNeighborhood _ _ _ _).mp (b.mem j)).2)
  rcases indexed_same_block ho with ⟨u,v,rfl,rfl⟩|⟨u,v,rfl,rfl⟩|⟨u,v,rfl,rfl⟩|⟨u,v,rfl,rfl⟩
  · exact congrArg Sum.inl (b.free.injective hij)
  · exact congrArg (fun a => Sum.inr (Sum.inl a)) (b.m.vertex.injective hij)
  · exact congrArg (fun a => Sum.inr (Sum.inr (Sum.inl a))) (b.x.vertex.injective hij)
  · exact congrArg (fun a => Sum.inr (Sum.inr (Sum.inr a))) (b.q.vertex.injective hij)

noncomputable def Blocks.frame {c : Host} {r : Vertex} (b : Blocks c r)
    (hd : colorDegree c (palette 0) r = 13) (hh : 47≤H c r) : PricingABD.BPhysicalBounds.Frame c where
  root := r
  vertex := indexEquiv.symm.toEmbedding.trans ⟨b.physical,b.physical_injective⟩
  ne_root i := ((mem_colorNeighborhood _ _ _ _).mp (b.mem (indexEquiv.symm i))).1
  spokes := by
    intro i
    change c r (b.physical (indexEquiv.symm i)) = palette (PricingABD.BPhysicalBounds.owner i)
    have h := ((mem_colorNeighborhood _ _ _ _).mp (b.mem (indexEquiv.symm i))).2
    simpa only [← owner_index,Equiv.apply_symm_apply] using h
  low_degree := hd
  selected := hh
  marked_high := by
    change b.physical (indexEquiv.symm 51) ∈ Incoming c r
    have h : indexEquiv.symm 51 = Sum.inr (Sum.inr (Sum.inr 15)) := by decide
    rw [h]
    exact b.marked_high

/-- Genuine ordered B roots admit the full52-vertex physical frame, with
all three complete critical blocks in their fixed native palettes. -/
theorem ordered_B_has_blocks (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : ∀ q : Color,colorDegree c (palette q) r = shape 1 q)
    (hh : 47≤H c r) : Nonempty (Blocks c r) := by
  classical
  have low : (colorNeighborhood c (palette 0) r).card = 13 := hd 0
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq (show 5≤(colorNeighborhood c (palette 0) r).card by omega)
  let se : S ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa using hcard)
  let free : Fin 5 ↪ Vertex := ⟨fun i => (se.symm i).val,fun i j he => se.symm.injective (Subtype.ext he)⟩
  obtain ⟨mark,hmark,hhigh,_⟩ := supplied_ABD_has_attaching_mark c hc r (palette 3) (hd 3) (by omega)
  obtain ⟨mt,m,hm⟩ := physical_k15_fixed_palette c hc r (palette 1) (hd 1) (foreignEquiv 1)
  obtain ⟨xt,x,hx⟩ := physical_k16_fixed_palette c hc r (palette 2) (hd 2) (foreignEquiv 2)
  obtain ⟨qt,q,hq,hmarked⟩ := physical_k16_marked_fixed_palette c hc r (palette 3) (hd 3) mark hmark (foreignEquiv 3)
  refine ⟨⟨free,mt,xt,qt,m,x,q,?_,hm,hx,hq,?_⟩⟩
  · intro i
    exact hS (se.symm i).property
  · rw [hmarked]
    apply (mem_highOwnNeighborSupport c r mark).mpr
    have hm' := (mem_colorNeighborhood _ _ _ _).mp hmark
    exact ⟨hm'.1,by simpa only [hm'.2] using hhigh⟩

#print axioms ordered_B_has_blocks
#print axioms Blocks.frame
end PricingIntegration.BActualFrame
