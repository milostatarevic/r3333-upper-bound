import UniformK60.EFormula

/-! The already used3/9 omission orbits, expressed as explicit mark-fixing
local actions. Every entry is checked against the complete16-template. -/
set_option autoImplicit false
namespace UniformK60.UUMarkedOmission

def index : (q : Bool) → Fin 15 → Fin (EFormula.omissionCount q)
  | false,r => (![0,1,2,0,2,0,1,0,2,1,1,1,2,2,0] : Fin 15 → Fin 3) r
  | true,r => (![0,1,2,0,3,4,5,6,2,7,7,1,8,3,6] : Fin 15 → Fin 9) r

def localBackward (q : Bool) (r : Fin 15) : Fin 16 → Fin 16 :=
  if q then (![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15]] : Fin 15 → Fin 16 → Fin 16) r
  else (![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![7,6,4,5,2,3,1,0,8,9,11,10,13,12,14,15],![5,9,2,14,12,0,11,7,13,1,10,6,4,8,3,15],![14,6,13,5,8,0,11,3,2,10,1,9,4,12,7,15],![7,11,12,0,2,14,9,5,13,1,6,10,8,4,3,15],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![5,9,2,14,12,0,11,7,13,1,10,6,4,8,3,15],![0,10,13,7,4,14,9,3,12,6,1,11,8,2,5,15],![7,11,12,0,2,14,9,5,13,1,6,10,8,4,3,15],![7,11,12,0,2,14,9,5,13,1,6,10,8,4,3,15],![0,10,13,7,4,14,9,3,12,6,1,11,8,2,5,15],![14,6,13,5,8,0,11,3,2,10,1,9,4,12,7,15]] : Fin 15 → Fin 16 → Fin 16) r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem local_bijective : ∀ q r, Function.Bijective (localBackward q r) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem local_preserves : ∀ q r a b, a≠b →
    R4333.k16Template q (localBackward q r a) (localBackward q r b)=R4333.k16Template q a b := by
  decide +kernel

theorem fixes_mark : ∀ q r, localBackward q r 15=15 := by decide +kernel

theorem moves_omission : ∀ q r,
    localBackward q r (EFormula.omissionPosition q (index q r)).castSucc=r.castSucc := by
  decide +kernel

noncomputable def localEquiv (q : Bool) (r : Fin 15) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (localBackward q r) (local_bijective q r)

#print axioms local_preserves
#print axioms moves_omission
end UniformK60.UUMarkedOmission
