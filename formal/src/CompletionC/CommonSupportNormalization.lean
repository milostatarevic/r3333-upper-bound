import CompletionC.CommonBlocks
import PricingIntegration.PairAdmissionData
set_option autoImplicit false
namespace CompletionC.CommonSupportNormalization
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.BActualFrame PricingIntegration.PhysicalForeignSupport
open PricingIntegration.NativeSupportConsumers PricingIntegration.PairAdmission
open CompletionC.CommonBlocks

def kindCode (large twisted:Bool):Nat:=if large then (if twisted then 3 else 2) else (if twisted then 1 else 0)

theorem support_card_invariant {n:Nat} {c:Host} {r mark:Vertex} {side:Bool}
 {t:R4333.EdgeColoring (Fin n) (Fin 3)}
 (m z:PhysicalNeighborhoodMap c r (palette (owner side)) t)
 (hm:mark∈colorNeighborhood c (palette 3) r):
 (support z mark).card=(support m mark).card:=by
 have he:=(support_image z hm).trans (support_image m hm).symm
 have hh:=congrArg Finset.card he
 simpa only [card_image_of_injective _ z.vertex.injective,card_image_of_injective _ m.vertex.injective] using hh

/-- Complete actual-host admission to the native support representatives.
The returned map is still a map of the entire original critical cell. -/
theorem normalize {c:Host} {r mark:Vertex} (large twisted side:Bool)
 (m:PhysicalNeighborhoodMap c r (palette (owner side)) (model large twisted))
 (hc:NoMonochromaticTriangle c) (hm:mark∈colorNeighborhood c (palette 3) r)
 (hp:m.colors=foreignEquiv (owner side)) (hh:15≤colorDegree c (palette 3) mark):
 ∃small:Bool,∃z:PhysicalNeighborhoodMap c r (palette (owner side)) (model large twisted),
 z.colors=foreignEquiv (owner side) ∧
 (support z mark).card=(if small then 4 else 5) ∧
 naturalSet (support z mark)∈reps (kindCode large twisted) small:=by
 cases large <;> cases twisted
 · rcases actual_u15_support_admitted m hc hm hp hh with ⟨hc0,rep,hr,z,hz,hs⟩|⟨hc0,rep,hr,z,hz,hs⟩
   · refine ⟨true,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingC.U15SupportCover.representatives4.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩
   · refine ⟨false,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingC.U15SupportCover.representatives5.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩
 · rcases actual_t15_support_admitted m hc hm hp hh with ⟨hc0,rep,hr,z,hz,hs⟩|⟨hc0,rep,hr,z,hz,hs⟩
   · refine ⟨true,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingABD.FiniteSupportsFast.representatives4.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩
   · refine ⟨false,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingABD.FiniteSupportsFast.representatives5.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩
 · rcases actual_u16_support_admitted m hc hm hp hh with ⟨hc0,rep,hr,z,hz,hs⟩|⟨hc0,rep,hr,z,hz,hs⟩
   · refine ⟨true,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingC.U16SupportCover.representatives4.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩
   · refine ⟨false,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingC.U16SupportCover.representatives5.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩
 · rcases actual_t16_support_admitted m hc hm hp hh with ⟨hc0,rep,hr,z,hz,hs⟩|⟨hc0,rep,hr,z,hz,hs⟩
   · refine ⟨true,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingABD.T16SupportCover.representatives4.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩
   · refine ⟨false,z,hz,(support_card_invariant m z hm).trans hc0,?_⟩
     change naturalSet (support z mark)∈PricingABD.T16SupportCover.representatives5.map naturalSet
     rw[hs];exact List.mem_map.mpr ⟨rep,hr,rfl⟩

def Normalized {c:Host} {l:Layout} {types:Types} (b:Blocks c l types) (sl sr:Bool):Prop:=
 (support (side:=false) b.left (b.marked.vertex 15)).card=(if sl then 4 else 5) ∧
 (support (side:=true) b.right (b.marked.vertex 15)).card=(if sr then 4 else 5) ∧
 naturalSet (support (side:=false) b.left (b.marked.vertex 15))∈reps (kindCode (leftLarge l) types.left) sl ∧
 naturalSet (support (side:=true) b.right (b.marked.vertex 15))∈reps (kindCode (rightLarge l) types.right) sr

theorem normalize_foreign {c:Host} {l:Layout} {types:Types} (b:Blocks c l types)
 (hc:NoMonochromaticTriangle c):
 ∃sl sr:Bool,∃z:Blocks c l types,z.root=b.root ∧ z.free=b.free ∧ z.marked.vertex=b.marked.vertex ∧
 Normalized z sl sr:=by
 obtain ⟨sl,ml,hpl,hl,hrl⟩:=normalize (leftLarge l) types.left false b.left hc
  (b.marked.mem_neighborhood 15) b.left_palette b.marked_high
 obtain ⟨sr,mr,hpr,hr,hrr⟩:=normalize (rightLarge l) types.right true b.right hc
  (b.marked.mem_neighborhood 15) b.right_palette b.marked_high
 let z:Blocks c l types:={b with left:=ml,right:=mr,left_palette:=hpl,right_palette:=hpr}
 exact ⟨sl,sr,z,rfl,rfl,rfl,hl,hr,hrl,hrr⟩
#print axioms normalize
#print axioms normalize_foreign
end CompletionC.CommonSupportNormalization
