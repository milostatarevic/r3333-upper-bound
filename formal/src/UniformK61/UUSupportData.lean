import CompletionC.NativeCatalogue
import CompletionC.CommonShapes
import PricingC.U15SupportCover

set_option autoImplicit false
namespace UniformK61.UUSupportData
open CompletionC.NativeMatrices
open PricingC.U15SupportCover
abbrev Pair := Fin 66

def shape (p : Pair) : Shape :=
 if p.val<9 then .freeFour else if p.val<33 then .leftFour
 else if p.val<57 then .rightFour else .allFive

def five (p : Pair) : Bool := decide (shape p ≠ .freeFour)

def leftCodes : Array Nat := #[666896,666896,666896,801552,801552,801552,763537,763537,763537,10753,10753,10753,11536,11536,11536,15120,15120,15120,15361,15361,15361,49179,49179,49179,12928,12928,12928,41681,41681,41681,42641,42641,42641,666896,666896,666896,666896,666896,666896,666896,666896,801552,801552,801552,801552,801552,801552,801552,801552,763537,763537,763537,763537,763537,763537,763537,763537,666896,666896,666896,801552,801552,801552,763537,763537,763537]
def rightCodes : Array Nat := #[666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,666896,801552,763537,10753,11536,15120,15361,49179,12928,41681,42641,10753,11536,15120,15361,49179,12928,41681,42641,10753,11536,15120,15361,49179,12928,41681,42641,666896,801552,763537,666896,801552,763537,666896,801552,763537]
def digit (code i : Nat) : Nat := code / 16^i % 16

def leftOrder (p : Pair) (i : Fin (shape p).left) : Fin 15 :=
 ⟨digit leftCodes[p.val]! i.val % 15,Nat.mod_lt _ (by decide)⟩
def rightOrder (p : Pair) (i : Fin (shape p).right) : Fin 15 :=
 ⟨digit rightCodes[p.val]! i.val % 15,Nat.mod_lt _ (by decide)⟩
def leftSet (p : Pair) : Finset (Fin 15) := Finset.univ.image (leftOrder p)
def rightSet (p : Pair) : Finset (Fin 15) := Finset.univ.image (rightOrder p)
def leftNats (p : Pair) : Finset Nat := (leftSet p).image Fin.val
def rightNats (p : Pair) : Finset Nat := (rightSet p).image Fin.val

def OrderOK (p : Pair) : Prop :=
 Function.Injective (leftOrder p) ∧ Function.Injective (rightOrder p) ∧
 (∀a b : Fin (shape p).left,a≠b → R4333.k15Untwisted (leftOrder p a) (leftOrder p b)=
   if PricingC.Rooted45Orientation.Cycle (shape p).left a.val b.val then 0 else 1) ∧
 (∀a b : Fin (shape p).right,a≠b → R4333.k15Untwisted (rightOrder p a) (rightOrder p b)=
   if PricingC.Rooted45Orientation.Cycle (shape p).right a.val b.val then 0 else 1)
instance (p : Pair) : Decidable (OrderOK p) := inferInstanceAs (Decidable (_ ∧ _))
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem orders_ok : ∀p : Pair, OrderOK p := by decide +kernel

def leftEmbedding (p : Pair) : Fin (shape p).left ↪ Fin 15 := ⟨leftOrder p,(orders_ok p).1⟩
def rightEmbedding (p : Pair) : Fin (shape p).right ↪ Fin 15 := ⟨rightOrder p,(orders_ok p).2.1⟩

def supports (n : Nat) : List (Finset (Fin 15)) := if n=4 then representatives4 else representatives5
def coverage (s : Shape) : Bool :=
 (supports s.left).all fun a => (supports s.right).all fun b =>
 (List.finRange 66).any fun p => decide (shape p=s ∧ leftSet p=a ∧ rightSet p=b)
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem coverage_ok : ∀s : Shape,coverage s=true := by decide +kernel

theorem pairs_cover : ∀s : Shape, ∀a∈supports s.left,∀b∈supports s.right,
 ∃p : Pair,shape p=s ∧ leftSet p=a ∧ rightSet p=b := by
 intro s a ha b hb
 have h := List.all_eq_true.mp (coverage_ok s) a ha
 have h' := List.all_eq_true.mp h b hb
 obtain ⟨p,_,hp⟩ := List.any_eq_true.mp h'
 exact ⟨p,of_decide_eq_true hp⟩

#print axioms orders_ok
#print axioms pairs_cover
end UniformK61.UUSupportData
