import PricingABD.P15PairOrbit

namespace PricingABD.P15MatrixTransport
open Ramsey61 Ramsey61.CEncodingCore PricingABD.TTExchange PricingABD.P15Encoder
open PricingABD.P15Suffix PricingABD.P15PairOrbit
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

def placementMap : Fin 14 → Fin 50 := ![0,1,2,3,4,5,17,6,14,19,20,32,21,29]
def placement : Fin 14 ↪ Fin 50 where
  toFun := placementMap
  inj' := by decide

/-- The entire four-row embedding is permuted; the underlying host stays fixed. -/
def reverseFrame {c : Host} {t : Bool} (f : Frame c 4 t) : Frame c 4 t where
  root := f.root
  free := reverseFourEquiv.toEmbedding.trans f.free
  left := f.left
  right := f.right
  marked := f.marked
  free_mem i := f.free_mem (reverseFour i)
  left_mem := f.left_mem
  right_mem := f.right_mem
  marked_mem := f.marked_mem
  left_edges := f.left_edges
  right_edges := f.right_edges
  marked_edges := f.marked_edges

set_option maxRecDepth 100000 in
theorem placement_reverse {c : Host} {t : Bool} (f : Frame c 4 t) (a : Fin 14) :
    physicalVertex (reverseFrame f) (placement a) =
      physicalVertex f (placement (reverseFourteen a)) := by fin_cases a <;> rfl

/-- Full original leaf in one fixed archived TT support pair. -/
def leaf (t : Bool) (j : Fin 300) : Sat.Fmla :=
  baseFmla t ++ suffix placement (matrix (word (representative j)))

/-- Every actual realization of one of the600catalogue matrices in this pair
satisfies an exact retained300-representative leaf after a whole-free-row action.
Only the matrix-catalogue entrance remains to turn this into a whole P15 cover. -/
theorem observed_pair000_has_retained_leaf {c : Host} {t : Bool} (f : Frame c 4 t)
    (hc : NoMonochromaticTriangle c) (i : Fin 600)
    (observed : ∀ a b, a ≠ b →
      c (physicalVertex f (placement a)) (physicalVertex f (placement b)) =
        palette (matrix (word (candidate i)) a b)) :
    ∃ valuation : Sat.Valuation, valuation.satisfies_fmla (leaf t (target i)) := by
  by_cases hr : useReverse i = true
  · have hword : word (representative (target i)) = fun e => word (candidate i) (crossPermutation e) := by
      funext e
      simpa [hr] using complete_pair000_edge_transport i e
    refine ⟨coloringValuation (physicalColoring (reverseFrame f)),?_⟩
    constructor
    intro clause hcl
    rcases List.mem_append.mp hcl with h | h
    · exact (frame_satisfies_exact_P15_base (reverseFrame f) hc).prop clause h
    · apply (suffix_satisfied (reverseFrame f) placement (matrix (word (representative (target i)))) ?_).prop clause h
      intro a b hab
      rw [placement_reverse,placement_reverse,hword,matrix_reverse]
      have hinj : Function.Injective reverseFourteen := by decide
      exact observed _ _ (hinj.ne hab)
  · have hf : useReverse i = false := Bool.eq_false_iff.mpr hr
    have hword : word (representative (target i)) = word (candidate i) := by
      funext e
      simpa [hf] using complete_pair000_edge_transport i e
    refine ⟨coloringValuation (physicalColoring f),?_⟩
    constructor
    intro clause hcl
    rcases List.mem_append.mp hcl with h | h
    · exact (frame_satisfies_exact_P15_base f hc).prop clause h
    · apply (suffix_satisfied f placement (matrix (word (representative (target i)))) ?_).prop clause h
      intro a b hab
      rw [hword]
      exact observed a b hab

#print axioms complete_pair000_edge_transport
#print axioms observed_pair000_has_retained_leaf
#check observed_pair000_has_retained_leaf
end PricingABD.P15MatrixTransport
