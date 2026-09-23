import Ramsey61.ABDTailBounds
import Ramsey61.CEncodingCore

set_option autoImplicit false
namespace PricingABD.ABLayout
open Ramsey61 Ramsey61.CEncodingCore

inductive Profile where
  | A | B | D
  deriving DecidableEq, Repr

/-- Native retained coordinates. D is included only for sharing the physical
and literal interface; the counter-program completion targets A and B. -/
structure Layout where
  profile : Profile
  five : Bool
  deriving DecidableEq, Repr

def freeSize (l : Layout) : Nat := if l.five then 5 else 4
def leftLarge (l : Layout) : Bool := decide (l.profile = .A)
def rightLarge (l : Layout) : Bool := decide (l.profile ≠ .D)
def leftSize (l : Layout) : Nat := if leftLarge l then 16 else 15
def rightSize (l : Layout) : Nat := if rightLarge l then 16 else 15
def tailSize (l : Layout) : Nat := leftSize l + rightSize l + 16
def lowSize (l : Layout) : Nat := 60 - tailSize l
def vertexCount (l : Layout) : Nat := freeSize l + tailSize l
def leftStart (l : Layout) : Nat := freeSize l
def rightStart (l : Layout) : Nat := freeSize l + leftSize l
def markedStart (l : Layout) : Nat := freeSize l + leftSize l + rightSize l

theorem sizes (l : Layout) :
    (freeSize l = 4 ∨ freeSize l = 5) ∧
    (leftSize l = 15 ∨ leftSize l = 16) ∧
    (rightSize l = 15 ∨ rightSize l = 16) ∧
    46 ≤ tailSize l ∧ tailSize l ≤ 48 ∧
    50 ≤ vertexCount l ∧ vertexCount l ≤ 53 ∧
    12 ≤ lowSize l ∧ lowSize l ≤ 14 := by
  rcases l with ⟨p,b⟩
  cases p <;> cases b <;> decide

def free (l : Layout) (i : Fin (freeSize l)) : Fin (vertexCount l) :=
  ⟨i.val, by have := sizes l; unfold vertexCount; omega⟩
def left (l : Layout) (i : Fin (leftSize l)) : Fin (vertexCount l) :=
  ⟨leftStart l + i.val, by have := sizes l; unfold vertexCount tailSize leftStart; omega⟩
def right (l : Layout) (i : Fin (rightSize l)) : Fin (vertexCount l) :=
  ⟨rightStart l + i.val, by unfold vertexCount tailSize rightStart; omega⟩
def marked (l : Layout) (i : Fin 16) : Fin (vertexCount l) :=
  ⟨markedStart l + i.val, by unfold vertexCount tailSize markedStart; omega⟩
def mark (l : Layout) : Fin (vertexCount l) := marked l 15
def tail (l : Layout) (i : Fin (tailSize l)) : Fin (vertexCount l) :=
  ⟨freeSize l + i.val, by unfold vertexCount; omega⟩
def owner (l : Layout) (i : Fin (vertexCount l)) : Fin 4 :=
  if i.val < freeSize l then 0 else
  if i.val < rightStart l then 1 else
  if i.val < markedStart l then 2 else 3

@[simp] theorem mark_val (l : Layout) : (mark l).val = vertexCount l - 1 := by
  have := sizes l
  unfold mark marked markedStart vertexCount tailSize
  simp only
  omega
@[simp] theorem owner_free (l : Layout) (i : Fin (freeSize l)) : owner l (free l i) = 0 := by
  simp [owner, free, i.isLt]
@[simp] theorem owner_left (l : Layout) (i : Fin (leftSize l)) : owner l (left l i) = 1 := by
  simp only [owner, left, leftStart, rightStart]
  split_ifs <;> omega
@[simp] theorem owner_right (l : Layout) (i : Fin (rightSize l)) : owner l (right l i) = 2 := by
  have := sizes l
  simp only [owner, right, rightStart, markedStart]
  split_ifs <;> omega
@[simp] theorem owner_marked (l : Layout) (i : Fin 16) : owner l (marked l i) = 3 := by
  have := sizes l
  simp only [owner, marked, rightStart, markedStart]
  split_ifs <;> omega
 theorem owner_tail_nonzero (l : Layout) (i : Fin (tailSize l)) : owner l (tail l i) ≠ 0 := by
  simp only [owner,tail]
  split_ifs <;> norm_num at * <;> omega

 theorem free_injective (l : Layout) : Function.Injective (free l) := by
  intro i j h
  have hv := congrArg (fun x : Fin (vertexCount l) => x.val) h
  exact Fin.ext hv
 theorem left_injective (l : Layout) : Function.Injective (left l) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [left] at this; omega
 theorem right_injective (l : Layout) : Function.Injective (right l) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [right] at this; omega
 theorem marked_injective (l : Layout) : Function.Injective (marked l) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [marked] at this; omega
 theorem tail_injective (l : Layout) : Function.Injective (tail l) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [tail] at this; omega

/-- All frame fields concern the same actual host and supplied root. Degree
bounds and all encoder facts are conclusions of later theorems, not fields. -/
structure Frame (c : Host) (l : Layout) where
  root : Fin 61
  vertex : Fin (vertexCount l) ↪ Fin 61
  ne_root : ∀ i, vertex i ≠ root
  spokes : ∀ i, c root (vertex i) = palette (owner l i)
  low_degree : colorDegree c (palette 0) root = lowSize l
  selected : tailSize l ≤ H c root
  marked_high : vertex (mark l) ∈ Incoming c root

structure Types where
  left : Bool
  right : Bool
  marked : Bool
  deriving DecidableEq, Repr

end PricingABD.ABLayout
