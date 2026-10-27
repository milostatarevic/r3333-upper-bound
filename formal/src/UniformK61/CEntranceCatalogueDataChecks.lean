import UniformK61.CEntranceCatalogueData
import UniformK61.CEntranceCover
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UniformK61.CEntrance.Catalogue
open CompletionC.NativeMatrices CompletionC.CommonSupportNormalization
open PricingIntegration.PairAdmission PricingC.NativePairActions

/-- Numeric predicate for exactly the three ordered pairs of critical types. -/
def Eligible (p : Fin 737) : Prop :=
  (retained p).family = 0 ∧
  ((retained p).leftKind=2 ∧ (retained p).rightKind=2 ∨
   (retained p).leftKind=2 ∧ (retained p).rightKind=3 ∨
   (retained p).leftKind=3 ∧ (retained p).rightKind=3)
instance (p : Fin 737) : Decidable (Eligible p) := inferInstanceAs (Decidable (_ ∧ _))

def headerFor (p : Fin 737) : Fin 21 := match p.val with
  | 733 => ⟨0,by decide⟩
  | 530 => ⟨1,by decide⟩
  | 542 => ⟨2,by decide⟩
  | 378 => ⟨3,by decide⟩
  | 454 => ⟨4,by decide⟩
  | 267 => ⟨5,by decide⟩
  | 540 => ⟨6,by decide⟩
  | 292 => ⟨7,by decide⟩
  | 293 => ⟨8,by decide⟩
  | 541 => ⟨9,by decide⟩
  | 585 => ⟨10,by decide⟩
  | 387 => ⟨11,by decide⟩
  | 265 => ⟨12,by decide⟩
  | 597 => ⟨13,by decide⟩
  | 598 => ⟨14,by decide⟩
  | 266 => ⟨15,by decide⟩
  | 0 => ⟨16,by decide⟩
  | 516 => ⟨17,by decide⟩
  | 517 => ⟨18,by decide⟩
  | 1 => ⟨19,by decide⟩
  | 524 => ⟨20,by decide⟩
  | _ => 0

/-- This checks every retained pair, not only the listed catalogue rows. -/
theorem all_eligible_headers : ∀ p : Fin 737, Eligible p → (header (headerFor p)).pair=p := by decide +kernel

theorem header_bounds : ∀ h : Fin 21,
  (header h).start+(header h).count ≤ 346 ∧
  (header h).count=(pairTable (header h).pair).count := by decide +kernel

def index (h : Fin 21) (j : Fin (header h).count) : Fin 346 :=
  ⟨(header h).start+j.val,by have := (header_bounds h).1;omega⟩

theorem index_row : ∀ (h : Fin 21) (j : Fin (header h).count),
  (row (index h j)).header=h ∧ (row (index h j)).repIndex=j.val := by decide +kernel

theorem header_metadata : ∀ h : Fin 21,
  (retained (header h).pair).family=0 ∧
  (retained (header h).pair).leftKind=kindCode true (header h).leftType ∧
  (retained (header h).pair).rightKind=kindCode true (header h).rightType ∧
  freeSize (header h).five=(pairTable (header h).pair).shape.free ∧
  ((header h).leftType=false ∨ (header h).rightType=true) ∧
  (retained (header h).pair).left=(header h).leftSupport ∧
  (retained (header h).pair).right=(header h).rightSupport ∧
  leftOrders[(header h).pair.val]! = (header h).leftOrder ∧
  rightOrders[(header h).pair.val]! = (header h).rightOrder ∧
  (pairTable (header h).pair).shape.code=(header h).shapeCode := by decide +kernel

theorem word_code : ∀ k : Fin 346,
  (pairTable (pair k)).representative (rep k)=(row k).wordCode := by decide +kernel

theorem exact_sizes : headers.size=21 ∧ rows.size=346 := by decide +kernel

#print axioms all_eligible_headers
#print axioms index_row
#print axioms header_metadata
#print axioms word_code
end UniformK61.CEntrance.Catalogue
