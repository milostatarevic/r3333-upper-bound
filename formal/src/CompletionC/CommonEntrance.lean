import CompletionC.CommonSupportNormalization
import PricingIntegration.ABActualOwners
import PricingG.DPhysicalSixEntrance
set_option autoImplicit false
namespace CompletionC.CommonEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open Ramsey61.CPhysicalNormalization
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.BActualFrame PricingIntegration.ABDRootPalette
open CompletionC.CommonBlocks

/-- Enumerate the entire physical free support; no subset is discarded. -/
noncomputable def of_cells {c:Host} (l:Layout) (types:Types) (r:Vertex)
 (left:PhysicalNeighborhoodMap c r (palette 1) (model (leftLarge l) types.left))
 (right:PhysicalNeighborhoodMap c r (palette 2) (model (rightLarge l) types.right))
 (marked:PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template types.marked))
 (hl:left.colors=foreignEquiv 1) (hr:right.colors=foreignEquiv 2)
 (hm:marked.colors=foreignEquiv 3)
 (hd:colorDegree c (palette 0) r=lowSize l) (hh:tailSize l≤H c r)
 (high:15≤colorDegree c (palette 3) (marked.vertex 15))
 (hs:(attachingSupport c r (palette 3) (marked.vertex 15) (palette 0)).card=freeSize l):
 Blocks c l types:=by
 classical
 let S:=attachingSupport c r (palette 3) (marked.vertex 15) (palette 0)
 let e:S≃Fin (freeSize l):=Fintype.equivFinOfCardEq (by simpa[S] using hs)
 let f:Fin (freeSize l)↪Vertex:=⟨fun i=>(e.symm i).val,fun i j h=>e.symm.injective (Subtype.ext h)⟩
 refine ⟨r,f,left,right,marked,?_,hl,hr,hm,hd,hh,high,?_,?_⟩
 · intro i;exact (mem_inter.mp (e.symm i).property).2
 · intro i;exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp (e.symm i).property).1).2
 · intro v;constructor
   · intro hv;refine ⟨e ⟨v,hv⟩,?_⟩
     change (e.symm (e ⟨v,hv⟩)).val=v
     simp
   · rintro ⟨i,rfl⟩;exact (e.symm i).property

@[simp] theorem of_cells_root {c:Host} (l:Layout) (types:Types) (r:Vertex)
 (left:PhysicalNeighborhoodMap c r (palette 1) (model (leftLarge l) types.left))
 (right:PhysicalNeighborhoodMap c r (palette 2) (model (rightLarge l) types.right))
 (marked:PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template types.marked))
 (hl:left.colors=foreignEquiv 1) (hr:right.colors=foreignEquiv 2) (hm:marked.colors=foreignEquiv 3)
 (hd:colorDegree c (palette 0) r=lowSize l) (hh:tailSize l≤H c r)
 (high:15≤colorDegree c (palette 3) (marked.vertex 15))
 (hs:(attachingSupport c r (palette 3) (marked.vertex 15) (palette 0)).card=freeSize l):
 (of_cells l types r left right marked hl hr hm hd hh high hs).root=r:=rfl

/-- Actual selected A roots reach a native owner using one global palette. -/
theorem actual_A (c:Host) (hc:NoMonochromaticTriangle c) (r:Vertex)
 (hw:W c r=48) (hh:48≤H c r):
 ∃σ:FourColor≃FourColor,let d:=relabel c (Equiv.refl _) σ
 NoMonochromaticTriangle d ∧ H d r=H c r ∧ W d r=W c r ∧
 ∃five:Bool,∃types:Types,∃b:Blocks d ⟨.A,five⟩ types,
 b.root=r ∧ (types.left=false∨types.right=true) ∧ (types.right=false∨types.marked=true):=by
 obtain ⟨σ,good,hH,hW,hd,a,h01,h12,m,hmp,high,hs⟩:=PricingIntegration.ABActualOwners.actual_A_native_owner c hc r hw hh
 refine ⟨σ,good,hH,hW,?_⟩
 have hh':48≤H (relabel c (Equiv.refl _) σ) r:=by rw[hH];exact hh
 let types:Types:=⟨a.types 0,a.types 1,a.types 2⟩
 rcases hs with hs|hs
 · refine ⟨false,types,of_cells ⟨.A,false⟩ types r (a.cell 0) (a.cell 1) m (a.palettes 0) (a.palettes 1) hmp (hd 0) hh' high hs,rfl,h01,h12⟩
 · refine ⟨true,types,of_cells ⟨.A,true⟩ types r (a.cell 0) (a.cell 1) m (a.palettes 0) (a.palettes 1) hmp (hd 0) hh' high hs,rfl,h01,h12⟩

/-- Actual selected B roots retain the native six-owner ordering. -/
theorem actual_B (c:Host) (hc:NoMonochromaticTriangle c) (r:Vertex)
 (hw:W c r=47) (hh:47≤H c r):
 ∃σ:FourColor≃FourColor,let d:=relabel c (Equiv.refl _) σ
 NoMonochromaticTriangle d ∧ H d r=H c r ∧ W d r=W c r ∧
 ∃five:Bool,∃types:Types,∃b:Blocks d ⟨.B,five⟩ types,
 b.root=r ∧ (types.right=false∨types.marked=true):=by
 obtain ⟨σ,good,hH,hW,hd,a,horder,m,hmp,high,hs⟩:=PricingIntegration.ABActualOwners.actual_B_native_owner c hc r hw hh
 refine ⟨σ,good,hH,hW,?_⟩
 have hh':47≤H (relabel c (Equiv.refl _) σ) r:=by rw[hH];exact hh
 let types:Types:=⟨a.mt,a.xt,a.qt⟩
 rcases hs with hs|hs
 · exact ⟨false,types,of_cells ⟨.B,false⟩ types r a.m a.x m a.mp a.xp hmp (hd 0) hh' high hs,rfl,horder⟩
 · exact ⟨true,types,of_cells ⟨.B,true⟩ types r a.m a.x m a.mp a.xp hmp (hd 0) hh' high hs,rfl,horder⟩

/-- D uses the existing six-owner physical entrance. The two U/U owners
remain explicit; they are not asserted to belong to the common737 route. -/
theorem actual_D (c:Host) (hc:NoMonochromaticTriangle c) (r:Vertex)
 (hw:W c r=46) (hh:46≤H c r):
 ∃σ:FourColor≃FourColor,let d:=relabel c (Equiv.refl _) σ
 NoMonochromaticTriangle d ∧ H d r=H c r ∧
 ∃five:Bool,∃types:Types,∃b:Blocks d ⟨.D,five⟩ types,
 b.root=r ∧ (types.left=false∨types.right=true):=by
 obtain ⟨σ,good,hH,hd,k,hk,a,horder⟩:=PricingG.DPhysicalBlocks.actual_D_native_physical c hc r hw hh
 refine ⟨σ,good,hH,?_⟩
 have hh':46≤H (relabel c (Equiv.refl _) σ) r:=by rw[hH];exact hh
 let types:Types:=⟨a.mType,a.xType,a.qType⟩
 have hs:(attachingSupport (relabel c (Equiv.refl _) σ) r (palette 3) (a.q.vertex 15) (palette 0)).card=k:=by
  have he:(attachingSupport (relabel c (Equiv.refl _) σ) r (palette 3) (a.q.vertex 15) (palette 0))=univ.image a.free:=by
   ext v;simp only [a.free_exact,mem_image,mem_univ,true_and]
  rw[he,card_image_of_injective _ a.free.injective,card_univ,Fintype.card_fin]
 rcases hk with hk|hk
 · exact ⟨false,types,of_cells ⟨.D,false⟩ types r a.m a.x a.q a.m_palette a.x_palette a.q_palette (hd 0) hh' a.marked_high (hs.trans hk),rfl,horder⟩
 · exact ⟨true,types,of_cells ⟨.D,true⟩ types r a.m a.x a.q a.m_palette a.x_palette a.q_palette (hd 0) hh' a.marked_high (hs.trans hk),rfl,horder⟩
#print axioms actual_A
#print axioms actual_B
#print axioms actual_D
end CompletionC.CommonEntrance
