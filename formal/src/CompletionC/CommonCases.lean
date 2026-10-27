import CompletionC.Common600

set_option autoImplicit false
namespace CompletionC.CommonCases
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission
open CompletionC.CommonSupportNormalization CompletionC.NativeMatrices

/-- The template ordering retained for each marked profile. -/
def NativeOwner (l : Layout) (t : Types) : Prop :=
  match l.profile with
  | .A => (t.left = false ∨ t.right = true) ∧ (t.right = false ∨ t.marked = true)
  | .B => t.right = false ∨ t.marked = true
  | .D => t.right = true

/-- A support-pair record has the required profile, template types and size. -/
def Compatible (l : Layout) (t : Types) (p : Fin 737) : Prop :=
  (retained p).family = familyCode l.profile ∧
  (retained p).leftKind = kindCode (leftLarge l) t.left ∧
  (retained p).rightKind = kindCode (rightLarge l) t.right ∧
  freeSize l = (pairTable p).shape.free

def Admitted (l : Layout) (t : Types) (p : Fin 737) : Prop :=
  NativeOwner l t ∧ Compatible l t p

theorem owner_common {l : Layout} {t : Types} (h : NativeOwner l t) : CommonOwner l t := by
  cases hp : l.profile <;> simp_all [NativeOwner, CommonOwner]

theorem source_compatible {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (p : Fin 737) (hf : freeSize l = (pairTable p).shape.free)
    (hp : retained p = sourceRecord b (pairTable p).shape) : Compatible l t p :=
  ⟨congrArg Record.family hp, congrArg Record.leftKind hp, congrArg Record.rightKind hp, hf⟩

deriving instance Fintype for Profile
deriving instance Fintype for Layout
deriving instance Fintype for Types

instance admittedDecidable (l : Layout) (t : Types) (p : Fin 737) :
    Decidable (Admitted l t p) := by
  unfold Admitted Compatible NativeOwner
  cases l.profile <;> infer_instance

/-- A case records a profile, template types, an admitted support pair and
one retained word. Formula semantics are supplied by the physical encoder. -/
abbrev Case := (l : Layout) × (t : Types) ×
  (p : {p : Fin 737 // Admitted l t p}) × Fin (pairTable p.val).count

end CompletionC.CommonCases
