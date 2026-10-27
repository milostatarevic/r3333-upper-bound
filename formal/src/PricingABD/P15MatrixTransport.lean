import PricingABD.P15PairOrbit

namespace PricingABD.P15MatrixTransport
open PricingABD.P15PairOrbit
open R4333.FiniteColorCNF

abbrev Word := Fin 65 → Fin 4

def crossIndex (a b : Fin 14) : Fin 65 :=
  ⟨(if a.val < 4 then if b.val < 9 then 5*a.val+(b.val-4)
    else 20+5*a.val+(b.val-9) else 40+5*(a.val-4)+(b.val-9)) % 65,
    Nat.mod_lt _ (by decide)⟩

def orderedMatrix (w : Word) (a b : Fin 14) : Fin 4 :=
  if b.val < 4 then (if b.val = a.val+1 then 1 else 2)
  else if a.val < 4 then w (crossIndex a b)
  else if b.val < 9 then (if b.val = a.val+1 ∨ (a.val=4 ∧ b.val=8) then 0 else 2)
  else if a.val < 9 then w (crossIndex a b)
  else (if b.val = a.val+1 ∨ (a.val=9 ∧ b.val=13) then 0 else 1)

def matrix (w : Word) (a b : Fin 14) : Fin 4 :=
  if a=b then 0 else if a<b then orderedMatrix w a b else orderedMatrix w b a

def reverseFour : Fin 4 → Fin 4 := ![3,2,1,0]
def reverseFourEquiv : Fin 4 ≃ Fin 4 where
  toFun := reverseFour
  invFun := reverseFour
  left_inv := by decide
  right_inv := by decide

def reverseFourteen : Fin 14 → Fin 14 := ![3,2,1,0,4,5,6,7,8,9,10,11,12,13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The cross-word permutation acts on all91physical matrix edges, including
internal P4/C5 edges; it is not merely a permutation of stored bytes. -/
theorem matrix_reverse (w : Word) (a b : Fin 14) :
    matrix (fun e => w (crossPermutation e)) a b =
      matrix w (reverseFourteen a) (reverseFourteen b) := by
  fin_cases a <;> fin_cases b <;>
    simp [matrix,orderedMatrix,crossIndex,crossPermutation,reverseFourteen]

def word (code : Nat) : Word := fun i => ⟨digit code i.val % 4,Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem complete_pair000_edge_transport : ∀ i : Fin 600, ∀ e : Fin 65,
    word (representative (target i)) e =
      word (candidate i) (if useReverse i then crossPermutation e else e) := by decide +kernel

#print axioms complete_pair000_edge_transport
end PricingABD.P15MatrixTransport
