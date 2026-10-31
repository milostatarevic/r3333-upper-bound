import UniformK60.ClassificationMarks
import UniformK60.BalancedEncodingBraceMaps

set_option autoImplicit false
namespace UniformK60.BalancedHostBraceMarked
open Ramsey61 UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.ClassificationAdapter UniformK60.ClassificationMarks
open UniformK60.BalancedEncodingBraces

theorem choices_complete : ∀ (t : Bool) (i : Fin 15),i∈markRepresentatives t →
    ∃ m : MarkChoice,markedKind m=t ∧ markedPosition m=i := by decide

def castMarked {c : Host} {root : Vertex} {a b : Bool} (h : a=b)
    (m : PhysicalNeighborhoodMap c root (palette 3) (R4333.k15Template a)) :
    PhysicalNeighborhoodMap c root (palette 3) (R4333.k15Template b) where
  vertex := m.vertex
  mem_neighborhood := m.mem_neighborhood
  covers_neighborhood := m.covers_neighborhood
  colors := m.colors
  map_color i j hij := by rw [←h];exact m.map_color i j hij

/-- All marked15 choices are exhausted by the three U and nine T orbits. -/
theorem actual_marked (c : Host) (hc : NoMonochromaticTriangle c) (root mark : Vertex)
    (hd : colorDegree c (palette 3) root=15)
    (hm : mark∈colorNeighborhood c (palette 3) root) :
    ∃ m : MarkChoice,∃ n : PhysicalNeighborhoodMap c root (palette 3) (R4333.k15Template (markedKind m)),
      n.colors=foreignEquiv 3 ∧ n.vertex (markedPosition m)=mark := by
  obtain ⟨t,i,hi,n,hn,hm⟩ := physical_k15_marked_fixed_palette c hc root (palette 3) hd mark hm (foreignEquiv 3)
  obtain ⟨m,hkind,hpos⟩ := choices_complete t i hi
  refine ⟨m,castMarked hkind.symm n,hn,?_⟩
  change n.vertex (markedPosition m)=mark
  rw [hpos]
  exact hm

noncomputable def markedMap {c : Host} {root : Vertex} {m : MarkChoice}
    (n : PhysicalNeighborhoodMap c root (palette 3) (R4333.k15Template (markedKind m))) : Fin 15↪Vertex :=
  (Equiv.ofBijective (markedOrder m) (markedOrder_bijective m)).toEmbedding.trans n.vertex

theorem markedMap_last {c : Host} {root mark : Vertex} {m : MarkChoice}
    (n : PhysicalNeighborhoodMap c root (palette 3) (R4333.k15Template (markedKind m)))
    (hmark : n.vertex (markedPosition m)=mark) : markedMap n 14=mark := by
  change n.vertex (markedOrder m 14)=mark
  rw [markedOrder_last,hmark]

#print axioms actual_marked
end UniformK60.BalancedHostBraceMarked
