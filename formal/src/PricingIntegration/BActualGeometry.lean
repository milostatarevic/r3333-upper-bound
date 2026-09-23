import PricingIntegration.FreeFiveCanonical
import PricingABD.BFixedGeometry

set_option autoImplicit false
namespace PricingIntegration.BActualGeometry
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.BActualFrame
open PricingABD.BPhysicalBounds PricingABD.BFixedGeometry

noncomputable def reorderFree {c : Host} {r : Vertex} (b : Blocks c r) (p : Equiv.Perm (Fin 5)) : Blocks c r :=
  { b with free := p.toEmbedding.trans b.free, free_mem := fun i => b.free_mem (p i) }

private theorem free_index : ∀ i : Fin 5,indexEquiv.symm (freeLabel i)=Sum.inl i := by decide
private theorem left_index : ∀ i : Fin 15,indexEquiv.symm (left i)=Sum.inr (Sum.inl i) := by decide
private theorem right_index : ∀ i : Fin 16,indexEquiv.symm (right i)=Sum.inr (Sum.inr (Sum.inl i)) := by decide
private theorem marked_index : ∀ i : Fin 16,indexEquiv.symm (marked i)=Sum.inr (Sum.inr (Sum.inr i)) := by decide

theorem frame_free {c : Host} {r : Vertex} (b : Blocks c r) (hd : colorDegree c (palette 0) r=13)
    (hh : 47≤H c r) (i : Fin 5) : (b.frame hd hh).vertex (freeLabel i)=b.free i := by
  change b.physical (indexEquiv.symm (freeLabel i))=_
  rw [free_index];rfl

theorem frame_left {c : Host} {r : Vertex} (b : Blocks c r) (hd : colorDegree c (palette 0) r=13)
    (hh : 47≤H c r) (i : Fin 15) : (b.frame hd hh).vertex (left i)=b.m.vertex i := by
  change b.physical (indexEquiv.symm (left i))=_
  rw [left_index];rfl

theorem frame_right {c : Host} {r : Vertex} (b : Blocks c r) (hd : colorDegree c (palette 0) r=13)
    (hh : 47≤H c r) (i : Fin 16) : (b.frame hd hh).vertex (right i)=b.x.vertex i := by
  change b.physical (indexEquiv.symm (right i))=_
  rw [right_index];rfl

theorem frame_marked {c : Host} {r : Vertex} (b : Blocks c r) (hd : colorDegree c (palette 0) r=13)
    (hh : 47≤H c r) (i : Fin 16) : (b.frame hd hh).vertex (marked i)=b.q.vertex i := by
  change b.physical (indexEquiv.symm (marked i))=_
  rw [marked_index];rfl

theorem pair_lt {n : Nat} {p : Fin n × Fin n} (hp : p∈pairs n) : p.1<p.2 := by
  obtain ⟨u,_,hm⟩ := List.mem_flatMap.mp hp
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
  exact of_decide_eq_true (List.mem_filter.mp hv).2

private theorem canonical_free_native : ∀ i j : Fin 5,i<j →
    foreign 3 (PricingC.Rooted555.canonical0 i j)=freeColor i j := by decide

theorem frame_fixed_geometry {c : Host} {r : Vertex} (b : Blocks c r)
    (hd : colorDegree c (palette 0) r=13) (hh : 47≤H c r)
    (ht : b.mType=true ∧ b.xType=true ∧ b.qType=true)
    (hcycle : ∀ i j,i≠j → c (b.free i) (b.free j)=palette (foreign 3 (PricingC.Rooted555.canonical0 i j)))
    (hattach : ∀ i,c (b.q.vertex 15) (b.free i)=palette 3) : FixedGeometry (b.frame hd hh) := by
  intro e he
  simp only [fixedEdges,List.mem_append] at he
  rcases he with (h|h)|h
  · simp only [templateEdges,List.mem_append] at h
    rcases h with (h|h)|h
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      rw [frame_left,frame_left,b.m.map_color _ _ (ne_of_lt (pair_lt hp)),b.m_palette,ht.1]
      rfl
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      rw [frame_right,frame_right,b.x.map_color _ _ (ne_of_lt (pair_lt hp)),b.x_palette,ht.2.1]
      rfl
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      rw [frame_marked,frame_marked,b.q.map_color _ _ (ne_of_lt (pair_lt hp)),b.q_palette,ht.2.2]
      exact (show ∀ q : Fin 3,(foreignEquiv 3 q).val=palette (markedColor q) from by decide) _
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
    rw [frame_free,frame_free,hcycle _ _ (ne_of_lt (pair_lt hp)),canonical_free_native _ _ (pair_lt hp)]
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    change c ((b.frame hd hh).vertex (marked 15)) ((b.frame hd hh).vertex (freeLabel i))=palette 3
    rw [frame_marked,frame_free,hattach]

/-- The representativeTTT/free5 prefix geometry is reached from an actual
marked support. The free C5 order is proved and only these five vertices are
reordered; it is not an additional mathematical assumption. -/
theorem actual_TTT_five_supplies_fixed_geometry {c : Host} {r : Vertex}
    (b : Blocks c r) (hc : NoMonochromaticTriangle c)
    (hd : colorDegree c (palette 0) r=13) (hh : 47≤H c r)
    (ht : b.mType=true ∧ b.xType=true ∧ b.qType=true)
    (hattach : ∀ i,c (b.q.vertex 15) (b.free i)=palette 3) :
    ∃ f : Frame c,f.root=r ∧ FixedGeometry f := by
  have hm := (mem_colorNeighborhood _ _ _ _).mp (b.q.mem_neighborhood 15)
  have high : 15≤colorDegree c (palette 3) (b.q.vertex 15) := by
    have h := ((mem_highOwnNeighborSupport c r _).mp b.marked_high).2
    simpa only [hm.2] using h
  have hr : r∈colorNeighborhood c (palette 3) (b.q.vertex 15) :=
    (colorNeighborhood_symm c (palette 3) r _ hm.1.symm).mp (b.q.mem_neighborhood 15)
  have hf : ∀ i,b.free i∈colorNeighborhood c (palette 3) (b.q.vertex 15) := by
    intro i
    refine (mem_colorNeighborhood _ _ _ _).mpr ⟨?_,hattach i⟩
    intro he
    have hi := ((mem_colorNeighborhood _ _ _ _).mp (b.free_mem i)).2
    rw [he,hm.2] at hi
    contradiction
  obtain ⟨p,hp⟩ := PricingIntegration.FreeFiveCanonical.actual_free_five_cycle c hc _ r high hr b.free b.free_mem hf
  let z := reorderFree b p
  refine ⟨z.frame hd hh,rfl,frame_fixed_geometry z hd hh ht hp ?_⟩
  intro i
  exact hattach (p i)

#print axioms actual_TTT_five_supplies_fixed_geometry
end PricingIntegration.BActualGeometry
