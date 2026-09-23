import PricingC.AnchoredScope

namespace PricingC.PairTables
open PricingC PricingC.AnchorTables PricingG.Completion72

def actionFn (i : Fin 10) : Fin 16 → Fin 16 :=
  match i.val with
  | 0 => ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 1 => ![0, 1, 15, 14, 8, 9, 7, 6, 4, 5, 11, 10, 12, 13, 3, 2]
  | 2 => ![0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1]
  | 3 => ![0, 2, 1, 3, 15, 13, 14, 12, 8, 10, 9, 11, 7, 5, 6, 4]
  | 4 => ![0, 4, 8, 12, 15, 11, 7, 3, 1, 5, 9, 13, 14, 10, 6, 2]
  | 5 => ![0, 4, 2, 6, 1, 5, 3, 7, 15, 11, 13, 9, 14, 10, 12, 8]
  | 6 => ![0, 8, 15, 7, 1, 9, 14, 6, 2, 10, 13, 5, 3, 11, 12, 4]
  | 7 => ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  | 8 => ![0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]
  | _ => ![0, 15, 8, 7, 4, 11, 12, 3, 2, 13, 10, 5, 6, 9, 14, 1]

def actionInv (i : Fin 10) : Fin 16 → Fin 16 :=
  match i.val with
  | 0 => ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 1 => ![0, 1, 15, 14, 8, 9, 7, 6, 4, 5, 11, 10, 12, 13, 3, 2]
  | 2 => ![0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]
  | 3 => ![0, 2, 1, 3, 15, 13, 14, 12, 8, 10, 9, 11, 7, 5, 6, 4]
  | 4 => ![0, 8, 15, 7, 1, 9, 14, 6, 2, 10, 13, 5, 3, 11, 12, 4]
  | 5 => ![0, 4, 2, 6, 1, 5, 3, 7, 15, 11, 13, 9, 14, 10, 12, 8]
  | 6 => ![0, 4, 8, 12, 15, 11, 7, 3, 1, 5, 9, 13, 14, 10, 6, 2]
  | 7 => ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  | 8 => ![0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1]
  | _ => ![0, 15, 8, 7, 4, 11, 12, 3, 2, 13, 10, 5, 6, 9, 14, 1]

def anchorActionFn (i : Fin 10) : Fin 5 → Fin 5 :=
  match i.val with
  | 0 => ![0, 1, 2, 3, 4]
  | 1 => ![0, 4, 3, 2, 1]
  | 2 => ![1, 2, 3, 4, 0]
  | 3 => ![1, 0, 4, 3, 2]
  | 4 => ![2, 3, 4, 0, 1]
  | 5 => ![2, 1, 0, 4, 3]
  | 6 => ![3, 4, 0, 1, 2]
  | 7 => ![3, 2, 1, 0, 4]
  | 8 => ![4, 0, 1, 2, 3]
  | _ => ![4, 3, 2, 1, 0]

set_option maxRecDepth 10000 in
private theorem action_left : ∀ i : Fin 10, Function.LeftInverse (actionInv i) (actionFn i) := by decide

set_option maxRecDepth 10000 in
private theorem action_right : ∀ i : Fin 10, Function.RightInverse (actionInv i) (actionFn i) := by decide

def action (i : Fin 10) : Fin 16 ≃ Fin 16 where
  toFun := actionFn i
  invFun := actionInv i
  left_inv := action_left i
  right_inv := action_right i

theorem action_anchor : ∀ (a : Fin 10) (j : Fin 5), action a (generators j) = generators (anchorActionFn a j) := by decide

theorem action_root : ∀ a : Fin 10, action a 0 = 0 := by decide

def representativeX : Fin 6 → Fin 72 := ![5, 5, 5, 5, 51, 51]

def representativeS : Fin 6 → Fin 72 := ![5, 28, 51, 56, 5, 51]

def pairRepresentative (i j : Fin 6) : Fin 6 :=
  (![0, 1, 1, 2, 3, 3, 1, 0, 3, 2, 1, 3, 1, 3, 0, 2, 3, 1, 4, 4, 4, 5, 4, 4, 3, 1, 3, 2, 0, 1, 3, 3, 1, 2, 1, 0] : Fin 36 → Fin 6) ⟨i.val * 6 + j.val,by omega⟩

def pairAction (i j : Fin 6) : Fin 10 :=
  (![0, 0, 9, 0, 0, 9, 3, 3, 3, 3, 4, 4, 6, 6, 5, 5, 5, 5, 0, 3, 5, 0, 7, 1, 7, 7, 8, 7, 7, 8, 2, 1, 2, 1, 1, 1] : Fin 36 → Fin 10) ⟨i.val * 6 + j.val,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_cover (i j : Fin 6) : ∀ u v : Fin 16, u ≠ v →
    referenceColor (anchoredIndex i) (action (pairAction i j) u) (action (pairAction i j) v) =
      referenceColor (representativeX (pairRepresentative i j)) u v ∧
    referenceColor (anchoredIndex j) (action (pairAction i j) u) (action (pairAction i j) v) =
      referenceColor (representativeS (pairRepresentative i j)) u v := by
  fin_cases i <;> fin_cases j <;> decide

#print axioms pair_cover
end PricingC.PairTables
