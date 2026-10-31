import UniformK60.NativeSupportIndex
import UniformK60.Core
import PricingIntegration.PairAdmissionData

/-! Canonical actual60 source facts for the entrance transport. Modes0/1
are the two C1 low-cell assignments; mode2 has its actual15 foreign cell
on the left. The marked13/14cell is never templated. -/
set_option autoImplicit false
namespace UniformK60.CEntranceSource
open Ramsey61 UniformK60.Physical
open CompletionC.NativeMatrices PricingIntegration.PairAdmission

abbrev Mode := Fin 3

def lowSize (mode : Mode) : Nat := if mode=0 then 13 else 14
def leftSize (mode : Mode) : Nat := if mode=2 then 15 else 16
def leftStart (mode : Mode) : Nat := 1+lowSize mode
def rightStart (mode : Mode) : Nat := leftStart mode+leftSize mode

def leftType (p : Fin 737) : Bool := decide ((retained p).leftKind % 2=1)
def rightType (p : Fin 737) : Bool := decide ((retained p).rightKind % 2=1)
def Eligible (mode : Mode) (p : Fin 737) : Prop :=
  (retained p).family=if mode=2 then 1 else 0
instance (mode : Mode) (p : Fin 737) : Decidable (Eligible mode p) := by
  unfold Eligible;infer_instance

def vertex (n : Nat) : Vertex := ⟨n%60,Nat.mod_lt _ (by decide)⟩
def leftVertex (mode : Mode) (i : Fin (leftSize mode)) : Vertex := vertex (leftStart mode+i.val)
def rightVertex (mode : Mode) (i : Fin 16) : Vertex := vertex (rightStart mode+i.val)

def rootColor (mode : Mode) (v : Vertex) : Color :=
  if v.val≤lowSize mode then 0 else if v.val<rightStart mode then 1
  else if v.val<rightStart mode+16 then 2 else 3

def matrixVertex (mode : Mode) (p : Fin 737) (a : Fin (pairTable p).shape.dimension) : Vertex :=
  if a.val<(pairTable p).shape.free then vertex (1+a.val)
  else if a.val<(pairTable p).shape.free+(pairTable p).shape.left then
    vertex (leftStart mode+PricingC.NativeBlockActions.digit
      PricingC.NativePairActions.leftOrders[p.val]! (a.val-(pairTable p).shape.free))
  else vertex (rightStart mode+PricingC.NativeBlockActions.digit
    PricingC.NativePairActions.rightOrders[p.val]!
      (a.val-(pairTable p).shape.free-(pairTable p).shape.left))

def coordinate (mode : Mode) (p : Fin 737) (v : Vertex) :
    Option (Fin (pairTable p).shape.dimension) :=
  (List.finRange (pairTable p).shape.dimension).find? fun a => matrixVertex mode p a==v

def member (mode : Mode) (p : Fin 737) (v : Vertex) : Bool :=
  if v=0 then true else if v.val≤(pairTable p).shape.free then true
  else if v.val≤lowSize mode then false
  else if v.val<rightStart mode then decide (v.val-leftStart mode∈(retained p).left)
  else if v.val<rightStart mode+16 then decide (v.val-rightStart mode∈(retained p).right)
  else false

def leftTemplate (mode : Mode) (t : Bool) :
    R4333.EdgeColoring (Fin (leftSize mode)) (Fin 3) :=
  if h : mode=2 then by simpa only [leftSize,h,if_pos] using R4333.k15Template t
  else by simpa [leftSize,h] using R4333.k16Template t

structure SourceWitness (mode : Mode) (p : Fin 737) (j : Fin (pairTable p).count)
    (c : Host) : Prop where
  good : NoMonochromaticTriangle c
  spokes : ∀ v : Vertex,v≠0 → c 0 v=palette (rootColor mode v)
  left : ∀ a b : Fin (leftSize mode),a≠b →
    c (leftVertex mode a) (leftVertex mode b)=
      palette (PricingABD.ABGeometry.foreign 1 (leftTemplate mode (leftType p) a b))
  right : ∀ a b : Fin 16,a≠b → c (rightVertex mode a) (rightVertex mode b)=
    palette (PricingABD.ABGeometry.foreign 2 (R4333.k16Template (rightType p) a b))
  membership : ∀ v : Vertex,v≠59 → (c v 59=palette 3 ↔ member mode p v=true)
  matrix : ∀ a b : Fin (pairTable p).shape.dimension,a≠b →
    c (matrixVertex mode p a) (matrixVertex mode p b)=
      palette (matrix (pairTable p).shape ((pairTable p).representative j) a b)

def fixedColor (mode : Mode) (p : Fin 737) (j : Fin (pairTable p).count)
    (a b : Vertex) : Option Color :=
  if a=0 then some (rootColor mode b)
  else if hleft : leftStart mode≤a.val ∧ b.val<rightStart mode then
    some (PricingABD.ABGeometry.foreign 1
      (leftTemplate mode (leftType p)
        ⟨(a.val-leftStart mode)%leftSize mode,Nat.mod_lt _ (by unfold leftSize;split_ifs <;> omega)⟩
        ⟨(b.val-leftStart mode)%leftSize mode,Nat.mod_lt _ (by unfold leftSize;split_ifs <;> omega)⟩))
  else if hright : rightStart mode≤a.val ∧ b.val<rightStart mode+16 then
    some (PricingABD.ABGeometry.foreign 2
      (R4333.k16Template (rightType p)
        ⟨(a.val-rightStart mode)%16,Nat.mod_lt _ (by decide)⟩
        ⟨(b.val-rightStart mode)%16,Nat.mod_lt _ (by decide)⟩))
  else match coordinate mode p a,coordinate mode p b with
  | some x,some y => if x≠y then
      some (matrix (pairTable p).shape ((pairTable p).representative j) x y) else none
  | _,_ => none

def sourceFact (mode : Mode) (p : Fin 737) (j : Fin (pairTable p).count)
    (u : Core.PhysicalUnit) : Bool :=
  let a := min u.u u.v
  let b := max u.u u.v
  decide (a<b) &&
    if u.positive then
      (fixedColor mode p j a b==some u.q) || ((u.q==3 && b==59) && member mode p a)
    else ((u.q==3 && b==59) && !(member mode p a))

end UniformK60.CEntranceSource
