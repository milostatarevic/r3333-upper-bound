import UniformK61.UUActionData

set_option autoImplicit false
namespace UniformK61.UUBridgeData
open UniformK61.Core
open PricingC.U15SupportCover

def freePairs : List (Nat × Nat) := [(194,194), (358,1334), (422,1014), (586,2154), (742,1398), (970,970), (1014,422), (1178,1946), (1334,358), (1398,742), (1726,1726), (1790,2110), (1946,1178), (2110,1790), (2154,586), (2382,2382), (2538,2538), (2586,2778), (2690,2690), (2702,2766), (2758,2582), (2766,2702), (2902,2886), (2930,2930)]
def autoInverse (a : Fin 10) : Fin 10 :=
 (#[ 0,1,7,3,4,9,6,2,8,5])[a.val]!

def RowOK (r : ActionRow) : Prop :=
 (r.freeCode,r.freeInverse)∈freePairs ∧
 r.leftInverse=autoInverse r.leftAuto ∧ r.rightInverse=autoInverse r.rightAuto
instance (r : ActionRow) : Decidable (RowOK r) := by unfold RowOK;infer_instance
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem rows_ok : ∀a : Action,RowOK (row a) := by decide +kernel

theorem free_inverse : ∀p∈freePairs,∀n : Fin 5,
 freeDigit p.1 (freeDigit p.2 n.val)=n.val ∧
 freeDigit p.2 (freeDigit p.1 n.val)=n.val := by decide +kernel

theorem auto_inverse : ∀a : Fin 10,∀v : Fin 15,
 autoMap a (autoMap (autoInverse a) v)=v ∧
 autoMap (autoInverse a) (autoMap a v)=v := by decide +kernel

theorem q_inverse : ∀q : Bool,∀v : Fin 16,
 qForward q (qBackward q v)=v ∧qBackward q (qForward q v)=v := by decide +kernel


end UniformK61.UUBridgeData
