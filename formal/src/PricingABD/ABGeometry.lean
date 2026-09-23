import PricingABD.ABLayout
import Ramsey61.ClassificationAdapter

set_option autoImplicit false
namespace PricingABD.ABGeometry
open Ramsey61 Ramsey61.CEncodingCore PricingABD.ABLayout

def model (large : Bool) (twisted : Bool) :
    R4333.EdgeColoring (Fin (if large then 16 else 15)) (Fin 3) :=
  match large with
  | true => R4333.k16Template twisted
  | false => R4333.k15Template twisted

def foreign (own : Fin 4) (q : Fin 3) : Fin 4 :=
  if q.val < own.val then ⟨q.val, by omega⟩ else ⟨q.val+1, by omega⟩

theorem foreign_injective (own : Fin 4) : Function.Injective (foreign own) := by
  intro q r h
  have hv := congrArg Fin.val h
  unfold foreign at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> apply Fin.ext <;> omega

theorem foreign_ne (own : Fin 4) (q : Fin 3) : foreign own q ≠ own := by
  intro h
  have hv := congrArg Fin.val h
  unfold foreign at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> omega

def freeColor (l : Layout) (u v : Fin (freeSize l)) : Fin 4 :=
  if (max u.val v.val = min u.val v.val + 1) ∨
    (l.five = true ∧ min u.val v.val = 0 ∧ max u.val v.val = 4) then 1 else 2

theorem freeColor_symm (l : Layout) (u v : Fin (freeSize l)) : freeColor l u v = freeColor l v u := by
  simp [freeColor, Nat.min_comm, Nat.max_comm]

/-- Concrete same-host color equations in native coordinates. No SAT,
reduction-completeness, counter or known-map hypothesis occurs here. -/
structure Geometry {c : Host} {l : Layout} (types : Types) (f : Frame c l) : Prop where
  left : ∀ u v : Fin (leftSize l), u ≠ v →
    c (f.vertex (ABLayout.left l u)) (f.vertex (ABLayout.left l v)) =
      palette (foreign 1 (model (leftLarge l) types.left u v))
  right : ∀ u v : Fin (rightSize l), u ≠ v →
    c (f.vertex (ABLayout.right l u)) (f.vertex (ABLayout.right l v)) =
      palette (foreign 2 (model (rightLarge l) types.right u v))
  marked : ∀ u v : Fin 16, u ≠ v →
    c (f.vertex (ABLayout.marked l u)) (f.vertex (ABLayout.marked l v)) =
      palette (foreign 3 (R4333.k16Template types.marked u v))
  free : ∀ u v : Fin (freeSize l), u ≠ v →
    c (f.vertex (ABLayout.free l u)) (f.vertex (ABLayout.free l v)) = palette (freeColor l u v)
  mark_free : ∀ u : Fin (freeSize l),
    c (f.vertex (mark l)) (f.vertex (ABLayout.free l u)) = palette 3

abbrev Edge (l : Layout) := Fin (vertexCount l) × Fin (vertexCount l) × Fin 4

def orderedPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u<v).map fun v => (u,v)

def templateEdges (l : Layout) (types : Types) : List (Edge l) :=
  (orderedPairs (leftSize l)).map (fun p =>
    (ABLayout.left l p.1, ABLayout.left l p.2, foreign 1 (model (leftLarge l) types.left p.1 p.2))) ++
  (orderedPairs (rightSize l)).map (fun p =>
    (ABLayout.right l p.1, ABLayout.right l p.2, foreign 2 (model (rightLarge l) types.right p.1 p.2))) ++
  (orderedPairs 16).map (fun p =>
    (ABLayout.marked l p.1, ABLayout.marked l p.2, foreign 3 (R4333.k16Template types.marked p.1 p.2)))

def freeEdges (l : Layout) : List (Edge l) :=
  (orderedPairs (freeSize l)).map fun p =>
    (ABLayout.free l p.1, ABLayout.free l p.2, freeColor l p.1 p.2)

def markEdges (l : Layout) : List (Edge l) :=
  (List.finRange (freeSize l)).map fun u => (mark l, ABLayout.free l u, 3)

def fixedEdges (l : Layout) (types : Types) : List (Edge l) :=
  templateEdges l types ++ freeEdges l ++ markEdges l

end PricingABD.ABGeometry
