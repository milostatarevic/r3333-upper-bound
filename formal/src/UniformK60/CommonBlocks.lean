import UniformK60.ClassificationSupportConsumers
import PricingABD.ABGeometry

/-!
One actual mark, two complete foreign neighborhoods, and its whole free
support. The marked root group is deliberately not templated here. This
is the common physical input for both15- and16-vertex marked groups and
for entrances from unclassified groups.
-/

set_option autoImplicit false
namespace UniformK60.CommonBlocks
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.ClassificationAdapter UniformK60.ClassificationGeometry
open PricingABD.ABLayout PricingABD.ABGeometry

structure Blocks (c : Host) (l : Layout) (types : Types) where
  root : Vertex
  mark : Vertex
  free : Fin (freeSize l) ↪ Vertex
  left : PhysicalNeighborhoodMap c root (palette 1) (model (leftLarge l) types.left)
  right : PhysicalNeighborhoodMap c root (palette 2) (model (rightLarge l) types.right)
  mark_mem : mark ∈ colorNeighborhood c (palette 3) root
  free_mem : ∀ i, free i ∈ colorNeighborhood c (palette 0) root
  left_palette : left.colors = foreignEquiv 1
  right_palette : right.colors = foreignEquiv 2
  marked_high : 15 ≤ colorDegree c (palette 3) mark
  free_own : ∀ i, c mark (free i) = palette 3
  free_exact : ∀ v, v ∈ attachingSupport c root (palette 3) mark (palette 0) ↔
    ∃ i, free i = v

/-- Only the free and foreign ranges are used by the finite word tables.
The remaining reference coordinates are totalized at the actual mark;
no injective placement or template is asserted on that unused range. -/
def physical {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (i : Fin (vertexCount l)) : Vertex :=
  if h0 : i.val < freeSize l then b.free ⟨i.val, h0⟩
  else if h1 : i.val < rightStart l then
    b.left.vertex ⟨i.val - leftStart l, by change i.val-leftStart l<leftSize l; unfold rightStart leftStart at *; omega⟩
  else if h2 : i.val < markedStart l then
    b.right.vertex ⟨i.val - rightStart l, by change i.val-rightStart l<rightSize l; unfold markedStart rightStart at *; omega⟩
  else b.mark

@[simp] theorem physical_free {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (i : Fin (freeSize l)) :
    physical b (PricingABD.ABLayout.free l i) = b.free i := by
  simp [physical, PricingABD.ABLayout.free, i.isLt]

@[simp] theorem physical_left {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (i : Fin (leftSize l)) :
    physical b (PricingABD.ABLayout.left l i) = b.left.vertex i := by
  have hi := i.isLt
  simp only [physical, PricingABD.ABLayout.left, leftStart, rightStart]
  split_ifs <;> try omega
  all_goals
    congr 1
    apply Fin.ext
    simp

@[simp] theorem physical_right {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (i : Fin (rightSize l)) :
    physical b (PricingABD.ABLayout.right l i) = b.right.vertex i := by
  have hi := i.isLt
  simp only [physical, PricingABD.ABLayout.right, leftStart, rightStart, markedStart]
  split_ifs <;> try omega
  all_goals
    congr 1
    apply Fin.ext
    simp

@[simp] theorem physical_marked {c : Host} {l : Layout} {t : Types}
    (b : Blocks c l t) (i : Fin 16) :
    physical b (PricingABD.ABLayout.marked l i) = b.mark := by
  simp only [physical, PricingABD.ABLayout.marked, leftStart, rightStart, markedStart]
  split_ifs <;> try omega
  rfl

/-- A coordinate reader, not an embedding of unused marked coordinates. -/
structure SupportFrame (c : Host) (l : Layout) where
  vertex : Fin (vertexCount l) → Vertex

def frame {c : Host} {l : Layout} {t : Types} (b : Blocks c l t) : SupportFrame c l :=
  ⟨physical b⟩

structure Geometry {c : Host} {l : Layout} (types : Types) (f : SupportFrame c l) : Prop where
  left : ∀ u v : Fin (leftSize l), u ≠ v →
    c (f.vertex (PricingABD.ABLayout.left l u)) (f.vertex (PricingABD.ABLayout.left l v)) =
      palette (PricingABD.ABGeometry.foreign 1 (model (leftLarge l) types.left u v))
  right : ∀ u v : Fin (rightSize l), u ≠ v →
    c (f.vertex (PricingABD.ABLayout.right l u)) (f.vertex (PricingABD.ABLayout.right l v)) =
      palette (PricingABD.ABGeometry.foreign 2 (model (rightLarge l) types.right u v))
  free : ∀ u v : Fin (freeSize l), u ≠ v →
    c (f.vertex (PricingABD.ABLayout.free l u)) (f.vertex (PricingABD.ABLayout.free l v)) =
      palette (freeColor l u v)
  mark_free : ∀ u : Fin (freeSize l),
    c (f.vertex (mark l)) (f.vertex (PricingABD.ABLayout.free l u)) = palette 3

private theorem native_palette (own : Fin 4) (q : Fin 3) :
    (foreignEquiv own q).val = palette (PricingABD.ABGeometry.foreign own q) := by
  fin_cases own <;> fin_cases q <;> rfl

theorem left_edges {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (u v : Fin (leftSize l)) (huv : u ≠ v) :
    c ((frame b).vertex (PricingABD.ABLayout.left l u))
      ((frame b).vertex (PricingABD.ABLayout.left l v)) =
      palette (PricingABD.ABGeometry.foreign 1 (model (leftLarge l) t.left u v)) := by
  change c (physical b _) (physical b _) = _
  rw [physical_left, physical_left, b.left.map_color u v huv, b.left_palette, native_palette]

theorem right_edges {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (u v : Fin (rightSize l)) (huv : u ≠ v) :
    c ((frame b).vertex (PricingABD.ABLayout.right l u))
      ((frame b).vertex (PricingABD.ABLayout.right l v)) =
      palette (PricingABD.ABGeometry.foreign 2 (model (rightLarge l) t.right u v)) := by
  change c (physical b _) (physical b _) = _
  rw [physical_right, physical_right, b.right.map_color u v huv, b.right_palette, native_palette]

end UniformK60.CommonBlocks
