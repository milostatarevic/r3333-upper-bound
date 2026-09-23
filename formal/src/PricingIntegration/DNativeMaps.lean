import PricingIntegration.DNativeMapData
import PricingIntegration.DNativeEdgeMap
import PricingIntegration.NativeRenaming

set_option autoImplicit false
namespace PricingIntegration.DNativeMaps
open PricingIntegration.NativePrimaryCore PricingIntegration.NativeRenaming

def fourSize : Nat := 4901
def fiveSize : Nat := 131571
def fourInverse (d : Nat) : Nat := if d=0 then 0 else DNativeEdgeMap.sparse 50 d
def fiveInverse (aux : Array (Array Nat)) (d : Nat) : Nat :=
  if d<5101 then (if d=0 then 0 else DNativeEdgeMap.sparse 51 d)
  else DNativeMapData.auxiliaryAt aux (d-5101)

def fourForward : Std.HashMap Nat Nat := forward fourSize fourInverse
def fiveForward : Std.HashMap Nat Nat :=
  let aux:=DNativeMapData.auxiliaryChunks
  forward fiveSize (fiveInverse aux)

def fourEncode : Nat → Nat := encode fourSize fourForward
def fiveEncode : Nat → Nat := encode fiveSize fiveForward
def fourDecode : Nat → Nat := decode fourSize fourInverse
def fiveDecode : Nat → Nat := decode fiveSize (fiveInverse DNativeMapData.auxiliaryChunks)

theorem four_roundtrip (a : Nat) : fourDecode (fourEncode a)=a := roundtrip _ _ a
theorem five_roundtrip (a : Nat) : fiveDecode (fiveEncode a)=a := roundtrip _ _ a

theorem four_decode_ordered (u v : Fin 50) (q : Fin 4) (huv : u<v) :
    fourDecode (orderedEdgeVar u v q)=R4333.FiniteColorCNF.edgeAtom u.val v.val q.val := by
  have hp:=(orderedEdgeVar_bounds (by decide : 50≤50 ∧ 50≤53) u v q huv).1
  have hb:=(orderedEdgeVar_bounds (by decide : 50≤50 ∧ 50≤53) u v q huv).2
  change orderedEdgeVar u v q<fourSize at hb
  rw [fourDecode,decode,if_pos hb,fourInverse,if_neg (by omega)]
  exact DNativeEdgeMap.ordered_roundtrip50 u v q huv

theorem five_decode_ordered (u v : Fin 51) (q : Fin 4) (huv : u<v) :
    fiveDecode (orderedEdgeVar u v q)=R4333.FiniteColorCNF.edgeAtom u.val v.val q.val := by
  have hp:=(orderedEdgeVar_bounds (by decide : 50≤51 ∧ 51≤53) u v q huv).1
  have hb:=(orderedEdgeVar_bounds (by decide : 50≤51 ∧ 51≤53) u v q huv).2
  have hb' : orderedEdgeVar u v q<5101:=hb
  have hsize : orderedEdgeVar u v q<fiveSize:=lt_trans hb' (by decide)
  rw [fiveDecode,decode,if_pos hsize,fiveInverse,if_pos hb',if_neg (by omega)]
  exact DNativeEdgeMap.ordered_roundtrip51 u v q huv

#print axioms four_roundtrip
#print axioms five_roundtrip
#print axioms five_decode_ordered
end PricingIntegration.DNativeMaps
