import UniformK61.CEntranceNormalize

set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore
open PricingIntegration.PhysicalForeignSupport PricingIntegration.PairAdmission
open CompletionC.CommonSupportNormalization CompletionC.NativeMatrices

/-- Only the finite foreign-support table index is shared with the (16,16)
row of the common cover. The actual host profile is supplied by Entrance. -/
def sourceRecord {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt) (s : Shape) : Record :=
  ⟨0,kindCode true lt,kindCode true rt,s.code,
    naturalSet (support (side:=false) b.left b.entrance.mark),
    naturalSet (support (side:=true) b.right b.entrance.mark)⟩

theorem native_header {lt rt : Bool} (h : Ordered lt rt) :
    (0,kindCode true lt,kindCode true rt) ∈ nativeHeaderKinds := by
  cases lt <;> cases rt <;> simp_all [Ordered,nativeHeaderKinds,kindCode]

/-- Exhaustive finite support-pair admission for two foreign K16 cells. No
assertion about a template or extension of the marked cell occurs here. -/
theorem normalized_admitted {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (hc : NoMonochromaticTriangle c) (sl sr : Bool) (hn : Normalized b sl sr)
    (ho : Ordered lt rt) :
    ∃ s : Shape, freeSize five = s.free ∧ (if sl then 4 else 5) = s.left ∧
      (if sr then 4 else 5) = s.right ∧
      ∃ p : Fin 737, NativeBinding p ∧ retained p = sourceRecord b s := by
  obtain ⟨s,hf,hl,hr⟩ := normalized_shape b hc sl sr hn
  have hsl : (s.code == 1) = sl := by cases s <;> cases sl <;> simp_all [Shape.left,Shape.code]
  have hsr : (s.code == 2) = sr := by cases s <;> cases sr <;> simp_all [Shape.right,Shape.code]
  have hb : s.code < 4 := by cases s <;> decide
  obtain ⟨rowid,hrow⟩ := native_header_present _ _ _ ⟨s.code,hb⟩ (native_header ho)
  have hleft : naturalSet (support (side:=false) b.left b.entrance.mark) ∈
      reps (row rowid).leftKind ((row rowid).stage == 1) := by
    rw [hrow]
    simpa only [hsl] using hn.2.2.1
  have hright : naturalSet (support (side:=true) b.right b.entrance.mark) ∈
      reps (row rowid).rightKind ((row rowid).stage == 2) := by
    rw [hrow]
    simpa only [hsr] using hn.2.2.2
  obtain ⟨p,hp,hadmit⟩ := native_support_product_admitted rowid _ _ hleft hright
  rw [hrow] at hadmit
  refine ⟨s,hf,hl,hr,p,hp,?_⟩
  rcases hadmit with he | ⟨hD,_,_,_⟩
  · exact he
  · contradiction

#print axioms normalized_admitted
end UniformK61.CEntrance
