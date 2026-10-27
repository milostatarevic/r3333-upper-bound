import UniformK61.CEntranceExtract
import PricingIntegration.PhysicalTypeTransport
import CompletionC.CommonPairAdmission

set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open Ramsey61.CPhysicalNormalization PricingABD.TTExchange
open PricingIntegration.BActualFrame PricingIntegration.PhysicalTypeTransport
open PricingIntegration.PhysicalForeignSupport PricingIntegration.PairAdmission
open CompletionC.CommonSupportNormalization CompletionC.NativeMatrices

/-- The two equal-size foreign cells may be exchanged by one global palette
permutation. No vertex is added to either order-fourteen cell. -/
def Entrance.exchange {c : Host} (e : Entrance c) : Entrance (swappedHost c) where
  root := e.root
  mark := e.mark
  degrees q := by
    rw [swappedHost,relabel_degree]
    fin_cases q
    · exact e.degrees 0
    · exact e.degrees 2
    · exact e.degrees 1
    · exact e.degrees 3
  mark_mem := (swappedHost_mem c _ _ _).mpr e.mark_mem
  marked_high := by
    rw [swappedHost,relabel_degree]
    exact e.marked_high

theorem blocks_exchange {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt) :
    Nonempty (Blocks (swappedHost c) five rt lt) := by
  obtain ⟨left,hl⟩ := k16_repalette (physical_relabel colorSwap (palette 1) b.right) (foreignEquiv 1)
  obtain ⟨right,hr⟩ := k16_repalette (physical_relabel colorSwap (palette 2) b.left) (foreignEquiv 2)
  refine ⟨⟨b.entrance.exchange,b.free,left,right,hl,hr,?_,?_,?_⟩⟩
  · intro i
    exact (swappedHost_mem c _ _ _).mpr (b.free_mem i)
  · intro i
    change colorSwap.symm (c b.entrance.mark (b.free i)) = palette 3
    rw [b.free_own i]
    rfl
  · intro v
    change v ∈ attachingSupport (swappedHost c) b.entrance.root (palette 3) b.entrance.mark (palette 0) ↔ _
    have h0 : colorSwap (palette 0) = palette 0 := by decide
    have h3 : colorSwap (palette 3) = palette 3 := by decide
    simpa only [attachingSupport,mem_inter,swappedHost_mem,h0,h3] using b.free_exact v

def Ordered (lt rt : Bool) : Prop := lt = false ∨ rt = true

/-- The finite boundary needs only UU, UT, TT. TU is obtained from UT by a
single host-wide exchange, including all edges incident to the low cells. -/
theorem ordered_blocks {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (hc : NoMonochromaticTriangle c) :
    ∃ d : Host, NoMonochromaticTriangle d ∧
      ∃ l r : Bool, Ordered l r ∧ Nonempty (Blocks d five l r) := by
  cases lt <;> cases rt
  · exact ⟨c,hc,false,false,Or.inl rfl,⟨b⟩⟩
  · exact ⟨c,hc,false,true,Or.inl rfl,⟨b⟩⟩
  · exact ⟨swappedHost c,swappedHost_good c hc,false,true,Or.inl rfl,blocks_exchange b⟩
  · exact ⟨c,hc,true,true,Or.inr rfl,⟨b⟩⟩

def Normalized {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt) (sl sr : Bool) : Prop :=
  (support (side:=false) b.left b.entrance.mark).card = (if sl then 4 else 5) ∧
  (support (side:=true) b.right b.entrance.mark).card = (if sr then 4 else 5) ∧
  naturalSet (support (side:=false) b.left b.entrance.mark) ∈ reps (kindCode true lt) sl ∧
  naturalSet (support (side:=true) b.right b.entrance.mark) ∈ reps (kindCode true rt) sr

theorem normalize_foreign {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (hc : NoMonochromaticTriangle c) :
    ∃ sl sr : Bool, ∃ z : Blocks c five lt rt,
      z.entrance = b.entrance ∧ z.free = b.free ∧ Normalized z sl sr := by
  obtain ⟨sl,ml,hpl,hl,hrl⟩ := normalize true lt false b.left hc
    b.entrance.mark_mem b.left_palette b.entrance.marked_high
  obtain ⟨sr,mr,hpr,hr,hrr⟩ := normalize true rt true b.right hc
    b.entrance.mark_mem b.right_palette b.entrance.marked_high
  let z : Blocks c five lt rt := {b with left:=ml,right:=mr,left_palette:=hpl,right_palette:=hpr}
  exact ⟨sl,sr,z,rfl,rfl,hl,hr,hrl,hrr⟩

theorem free_card {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt) :
    (attachingSupport c b.entrance.root (palette 3) b.entrance.mark (palette 0)).card = freeSize five := by
  have he : attachingSupport c b.entrance.root (palette 3) b.entrance.mark (palette 0) = univ.image b.free := by
    ext v
    simp only [b.free_exact,mem_image,mem_univ,true_and]
  rw [he,card_image_of_injective _ b.free.injective,card_univ,Fintype.card_fin]

theorem normalized_shape {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (hc : NoMonochromaticTriangle c) (sl sr : Bool) (hn : Normalized b sl sr) :
    ∃ s : Shape, freeSize five = s.free ∧
      (if sl then 4 else 5) = s.left ∧ (if sr then 4 else 5) = s.right := by
  have hp := support_shape b.entrance hc
  have hl := congrArg Finset.card (support_image (side:=false) b.left b.entrance.mark_mem)
  have hr := congrArg Finset.card (support_image (side:=true) b.right b.entrance.mark_mem)
  rw [card_image_of_injective _ b.left.vertex.injective] at hl
  rw [card_image_of_injective _ b.right.vertex.injective] at hr
  change (support (side:=false) b.left b.entrance.mark).card =
    (attachingSupport c b.entrance.root (palette 3) b.entrance.mark (palette 1)).card at hl
  change (support (side:=true) b.right b.entrance.mark).card =
    (attachingSupport c b.entrance.root (palette 3) b.entrance.mark (palette 2)).card at hr
  rw [free_card b,←hl,←hr,hn.1,hn.2.1] at hp
  unfold FourFivePattern at hp
  cases five <;> cases sl <;> cases sr <;> simp only [freeSize,Bool.false_eq_true,↓reduceIte] at hp
  · exact ⟨.freeFour,rfl,rfl,rfl⟩
  · omega
  · omega
  · omega
  · exact ⟨.allFive,rfl,rfl,rfl⟩
  · exact ⟨.rightFour,rfl,rfl,rfl⟩
  · exact ⟨.leftFour,rfl,rfl,rfl⟩
  · omega

#print axioms blocks_exchange
#print axioms normalize_foreign
#print axioms normalized_shape
end UniformK61.CEntrance
