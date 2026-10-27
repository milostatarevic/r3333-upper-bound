import UniformK61.Core
import CompletionC.CommonSupportNormalization
import CompletionC.NativeCatalogue

set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingIntegration.BActualFrame

/-- Common colors: free 0, foreign 1 and 2, marked 3. Both low cells have
fourteen actual vertices; no critical template on either is assumed. -/
def rootSize : Color → Nat := ![14,16,16,14]

structure Entrance (c : Host) where
  root : Vertex
  mark : Vertex
  degrees : ∀ q : Color, colorDegree c (palette q) root = rootSize q
  mark_mem : mark ∈ colorNeighborhood c (palette 3) root
  marked_high : 15 ≤ colorDegree c (palette 3) mark

def freeSize (five : Bool) : Nat := if five then 5 else 4

/-- Two complete foreign templates and the entire actual free support of
the mark. The marked root cell is still untemplated. -/
structure Blocks (c : Host) (five leftType rightType : Bool) where
  entrance : Entrance c
  free : Fin (freeSize five) ↪ Vertex
  left : PhysicalNeighborhoodMap c entrance.root (palette 1) (R4333.k16Template leftType)
  right : PhysicalNeighborhoodMap c entrance.root (palette 2) (R4333.k16Template rightType)
  left_palette : left.colors = foreignEquiv 1
  right_palette : right.colors = foreignEquiv 2
  free_mem : ∀ i, free i ∈ colorNeighborhood c (palette 0) entrance.root
  free_own : ∀ i, c entrance.mark (free i) = palette 3
  free_exact : ∀ v, v ∈ attachingSupport c entrance.root (palette 3) entrance.mark (palette 0) ↔
    ∃ i, free i = v

end UniformK61.CEntrance
