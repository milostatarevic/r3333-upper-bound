import PricingG.DPhysicalBlocks

set_option autoImplicit false
namespace PricingG.DPhysicalBlocks
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open Ramsey61.CPhysicalNormalization
open PricingIntegration.BActualFrame
open PricingABD.TTExchange

private theorem swap_pal12 (a : Fin 3) : colorSwap.symm (foreignEquiv 2 a).val = (foreignEquiv 1 a).val := by fin_cases a <;> rfl
private theorem swap_pal21 (a : Fin 3) : colorSwap.symm (foreignEquiv 1 a).val = (foreignEquiv 2 a).val := by fin_cases a <;> rfl
private theorem swap_pal3 (a : Fin 3) : colorSwap.symm (foreignEquiv 3 (localSwap a)).val = (foreignEquiv 3 a).val := by fin_cases a <;> decide

noncomputable def Blocks.exchangeM {c : Host} {r : Vertex} {k : Nat} (b : Blocks c r k) :
    PhysicalNeighborhoodMap (swappedHost c) r (palette 1) (R4333.k15Template b.xType) where
  vertex := b.x.vertex
  mem_neighborhood i := (swappedHost_mem _ _ _ _).mpr (b.x.mem_neighborhood i)
  covers_neighborhood v hv := b.x.covers_neighborhood v ((swappedHost_mem _ _ _ _).mp hv)
  colors := foreignEquiv 1
  map_color a d had := by
    change colorSwap.symm (c (b.x.vertex a) (b.x.vertex d)) = _
    rw [b.x.map_color a d had,b.x_palette,swap_pal12]

noncomputable def Blocks.exchangeX {c : Host} {r : Vertex} {k : Nat} (b : Blocks c r k) :
    PhysicalNeighborhoodMap (swappedHost c) r (palette 2) (R4333.k15Template b.mType) where
  vertex := b.m.vertex
  mem_neighborhood i := (swappedHost_mem _ _ _ _).mpr (b.m.mem_neighborhood i)
  covers_neighborhood v hv := b.m.covers_neighborhood v ((swappedHost_mem _ _ _ _).mp hv)
  colors := foreignEquiv 2
  map_color a d had := by
    change colorSwap.symm (c (b.m.vertex a) (b.m.vertex d)) = _
    rw [b.m.map_color a d had,b.m_palette,swap_pal21]

noncomputable def Blocks.exchangeQ {c : Host} {r : Vertex} {k : Nat} (b : Blocks c r k) :
    PhysicalNeighborhoodMap (swappedHost c) r (palette 3) (R4333.k16Template b.qType) where
  vertex := (markedQMap b.qType).toEmbedding.trans b.q.vertex
  mem_neighborhood i := (swappedHost_mem _ _ _ _).mpr (b.q.mem_neighborhood (markedQMap b.qType i))
  covers_neighborhood v hv := by
    obtain ⟨i,hi⟩ := b.q.covers_neighborhood v ((swappedHost_mem _ _ _ _).mp hv)
    refine ⟨(markedQMap b.qType).symm i,?_⟩
    change b.q.vertex (markedQMap b.qType ((markedQMap b.qType).symm i)) = v
    simpa only [Equiv.apply_symm_apply] using hi
  colors := foreignEquiv 3
  map_color a d had := by
    change colorSwap.symm (c (b.q.vertex (markedQMap b.qType a)) (b.q.vertex (markedQMap b.qType d))) = _
    rw [b.q.map_color _ _ ((markedQMap b.qType).injective.ne had),b.q_palette,
      markedQMap_preserves _ _ _ had,swap_pal3]

@[simp] theorem Blocks.exchangeQ_mark {c : Host} {r : Vertex} {k : Nat} (b : Blocks c r k) :
    b.exchangeQ.vertex 15 = b.q.vertex 15 := by
  change b.q.vertex (markedQMap b.qType 15) = _
  rw [markedQMap_fixes]

/-- The full physical swap for arbitrary U/T kinds, preserving every actual
vertex map except the necessary simultaneous whole-Q coordinate change. -/
noncomputable def Blocks.exchange {c : Host} {r : Vertex} {k : Nat} (b : Blocks c r k) :
    Blocks (swappedHost c) r k where
  free := b.free
  mType := b.xType
  xType := b.mType
  qType := b.qType
  m := b.exchangeM
  x := b.exchangeX
  q := b.exchangeQ
  free_mem i := (swappedHost_mem _ _ _ _).mpr (b.free_mem i)
  m_palette := rfl
  x_palette := rfl
  q_palette := rfl
  marked_high := by
    rw [b.exchangeQ_mark]
    change 15 ≤ colorDegree (relabel c (Equiv.refl _) colorSwap) (palette 3) (b.q.vertex 15)
    rw [relabel_degree]
    exact b.marked_high
  free_own i := by
    rw [b.exchangeQ_mark,swappedHost_apply,b.free_own]
    rfl
  free_exact v := by
    rw [b.exchangeQ_mark]
    have h : attachingSupport (swappedHost c) r (palette 3) (b.q.vertex 15) (palette 0) =
        attachingSupport c r (palette 3) (b.q.vertex 15) (palette 0) := by
      ext u
      simp only [attachingSupport,Finset.mem_inter,swappedHost_mem]
      rfl
    rw [h]
    exact b.free_exact v

/-- Sorting the two equal-sized foreign types gives exactlyUU,UT,TT, while
Q retains either type. This is one global palette permutation of one host. -/
theorem physical_native_owner {c : Host} {r : Vertex} {k : Nat} (b : Blocks c r k) :
    (b.mType = false ∨ b.xType = true) ∨
      (b.exchange.mType = false ∧ b.exchange.xType = true ∧
       b.exchange.qType = b.qType ∧ b.exchange.q.vertex 15 = b.q.vertex 15) := by
  cases hm : b.mType <;> cases hx : b.xType
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr ⟨hx,hm,rfl,b.exchangeQ_mark⟩
  · exact Or.inl (Or.inr rfl)

#print axioms Blocks.exchange
#print axioms physical_native_owner
end PricingG.DPhysicalBlocks
