import CompletionC.CommonSupportNormalization
import CompletionC.NativeMatrices
set_option autoImplicit false
namespace CompletionC.CommonShapes
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingABD.ABLayout
open PricingIntegration.PhysicalForeignSupport
open CompletionC.CommonBlocks CompletionC.CommonSupportNormalization CompletionC.NativeMatrices

theorem free_card {c:Host} {l:Layout} {types:Types} (b:Blocks c l types):
 (attachingSupport c b.root (palette 3) (b.marked.vertex 15) (palette 0)).card=freeSize l:=by
 have he:attachingSupport c b.root (palette 3) (b.marked.vertex 15) (palette 0)=univ.image b.free:=by
  ext v;simp only[b.free_exact,mem_image,mem_univ,true_and]
 rw[he,card_image_of_injective _ b.free.injective,card_univ,Fintype.card_fin]

theorem support_sum {c:Host} {l:Layout} {types:Types} (b:Blocks c l types)
 (hc:NoMonochromaticTriangle c):
 colorDegree c (palette 3) (b.marked.vertex 15)-1=
 freeSize l+(support (side:=false) b.left (b.marked.vertex 15)).card+
 (support (side:=true) b.right (b.marked.vertex 15)).card:=by
 have hp:=attachingSupport_partition c hc b.root (palette 3) (b.marked.vertex 15) (b.marked.mem_neighborhood 15)
 have he:(univ:Finset FourColor).erase (palette 3)={palette 0,palette 1,palette 2}:=by decide
 rw[he] at hp
 have he2 (f:FourColor→Nat):∑p∈({palette 0,palette 1,palette 2}:Finset FourColor),f p=f (palette 0)+(f (palette 1)+f (palette 2)):=by
  simp [palette]
 rw[he2] at hp
 have hl:=congrArg Finset.card (support_image (side:=false) b.left (b.marked.mem_neighborhood 15))
 have hr:=congrArg Finset.card (support_image (side:=true) b.right (b.marked.mem_neighborhood 15))
 rw[card_image_of_injective _ b.left.vertex.injective] at hl
 rw[card_image_of_injective _ b.right.vertex.injective] at hr
 change (support (side:=false) b.left (b.marked.vertex 15)).card=(attachingSupport c b.root (palette 3) (b.marked.vertex 15) (palette 1)).card at hl
 change (support (side:=true) b.right (b.marked.vertex 15)).card=(attachingSupport c b.root (palette 3) (b.marked.vertex 15) (palette 2)).card at hr
 rw[free_card b,←hl,←hr] at hp
 omega

/-- The actual high marked vertex permits exactly the four retained shapes.
It rules out two small supports without assuming any catalogue coverage. -/
theorem normalized_shape {c:Host} {l:Layout} {types:Types} (b:Blocks c l types)
 (hc:NoMonochromaticTriangle c) (sl sr:Bool) (hn:Normalized b sl sr):
 ∃s:Shape,freeSize l=s.free ∧ (if sl then 4 else 5)=s.left ∧ (if sr then 4 else 5)=s.right:=by
 have hp:=support_sum b hc
 rw[hn.1,hn.2.1] at hp
 have hh:=b.marked_high
 cases h:l.five <;> cases sl <;> cases sr
 · exact ⟨.freeFour,by simp[freeSize,h,Shape.free],rfl,rfl⟩
 · simp [freeSize,h] at hp;omega
 · simp [freeSize,h] at hp;omega
 · simp [freeSize,h] at hp;omega
 · exact ⟨.allFive,by simp[freeSize,h,Shape.free],rfl,rfl⟩
 · exact ⟨.rightFour,by simp[freeSize,h,Shape.free],rfl,rfl⟩
 · exact ⟨.leftFour,by simp[freeSize,h,Shape.free],rfl,rfl⟩
 · simp [freeSize,h] at hp;omega
#print axioms support_sum
#print axioms normalized_shape
end CompletionC.CommonShapes
