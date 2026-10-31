import UniformK60.CEntranceSourceDefs
import UniformK60.CEntranceFormula
import UniformK60.UnitTransport

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
open UniformK60.Physical UniformK60.CEntranceSource
open CompletionC.NativeMatrices

structure Entry where
  mode : Mode
  pair : Fin 737
  repNat : Nat
  target : CEntranceFormula.SourceCase
  omission : UnitRestriction.Omission
  toSourceCode : Nat
  toTargetCode : Nat
  swap : Bool
  deriving Inhabited

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem count_positive : ∀ p : Fin 737,0<(pairTable p).count := by decide +kernel

def rep (e : Entry) : Fin (pairTable e.pair).count :=
  ⟨e.repNat%(pairTable e.pair).count,Nat.mod_lt _ (count_positive _)⟩

def vertexMap (code : Nat) (v : Vertex) : Vertex :=
  ⟨((code >>> (6*v.val)) &&& 63)%60,Nat.mod_lt _ (by decide)⟩

def colorMap (e : Entry) : Color ≃ Color :=
  if e.swap then Equiv.swap 1 2 else Equiv.refl _

def pullUnit (e : Entry) (u : Core.PhysicalUnit) : Core.PhysicalUnit :=
  ⟨u.positive,vertexMap e.toSourceCode u.u,vertexMap e.toSourceCode u.v,(colorMap e).symm u.q⟩

def targetUnits (e : Entry) : List Core.PhysicalUnit :=
  UnitRestriction.restrictUnits e.omission (CEntranceFormula.referenceUnits e.target)

def TargetLegal (e : Entry) : Prop :=
  if e.mode=2 then CEntranceFormula.c2Allowed e.target e.omission
  else e.omission=CEntranceFormula.c1Omission (e.target,decide (e.mode=1))

instance (e : Entry) : Decidable (TargetLegal e) := by unfold TargetLegal;infer_instance

/-- Both complete coordinate maps and every signed target fact are checked.
The source predicate has no marked13/14-cell template assumptions. -/
def Valid (e : Entry) : Prop :=
  Eligible e.mode e.pair ∧ e.repNat<(pairTable e.pair).count ∧ TargetLegal e ∧
  (∀ v : Vertex,
    vertexMap e.toTargetCode (vertexMap e.toSourceCode v)=v ∧
    vertexMap e.toSourceCode (vertexMap e.toTargetCode v)=v) ∧
  (targetUnits e).all (fun u => sourceFact e.mode e.pair (rep e) (pullUnit e u))=true

instance (e : Entry) : Decidable (Valid e) := by unfold Valid;infer_instance

def vertexEquiv (e : Entry) (h : Valid e) : Vertex ≃ Vertex where
  toFun := vertexMap e.toSourceCode
  invFun := vertexMap e.toTargetCode
  left_inv v := ((h.2.2.2.1) v).1
  right_inv v := ((h.2.2.2.1) v).2

theorem rep_value (e : Entry) (h : Valid e) : (rep e).val=e.repNat :=
  Nat.mod_eq_of_lt h.2.1

end UniformK60.CEntranceBridge
