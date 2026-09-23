import PricingC.DegreeFourPathData

namespace PricingC.DegreeFourPath
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingIntegration.FixedPhysicalNeighborhood PricingIntegration.BActualFrame

private theorem palette_three (a:Fin 3):(foreignEquiv 3 a).val=palette a.castSucc:=by fin_cases a <;> rfl

theorem physical_support_image {n:Nat} {c:Host} {mark r:Vertex}
 {template:R4333.EdgeColoring (Fin n) (Fin 3)}
 (m:PhysicalNeighborhoodMap c mark (palette 3) template) (hpal:m.colors=foreignEquiv 3)
 (v:Fin n) (hv:m.vertex v=r) (q:Fin 3):
 (R4333.colorNeighborhood template q v).image m.vertex=
 attachingSupport c r (palette 3) mark (palette q.castSucc):=by
 ext w
 constructor
 · rintro hw
   obtain ⟨j,hj,rfl⟩:=mem_image.mp hw
   have hj':=(R4333.mem_colorNeighborhood _ _ _ _).mp hj
   apply mem_inter.mpr
   refine ⟨m.mem_neighborhood j,?_⟩
   apply (mem_colorNeighborhood _ _ _ _).mpr
   refine ⟨?_,?_⟩
   · rw[←hv]
     exact m.vertex.injective.ne hj'.1
   · rw[←hv,m.map_color v j hj'.1.symm,hpal,hj'.2,palette_three]
 · intro hw
   obtain ⟨hmark,hroot⟩:=mem_inter.mp hw
   obtain ⟨j,rfl⟩:=m.covers_neighborhood w hmark
   have hroot':=(mem_colorNeighborhood _ _ _ _).mp hroot
   have hj:j≠v:=by intro he;subst j;exact hroot'.1 hv
   apply mem_image.mpr
   refine ⟨j,?_,rfl⟩
   apply (R4333.mem_colorNeighborhood _ _ _ _).mpr
   refine ⟨hj,?_⟩
   have hm:=m.map_color v j hj.symm
   rw[hv,hpal,palette_three] at hm
   have hp:=palette_injective (hm.symm.trans hroot'.2)
   exact Fin.ext (congrArg (fun x:Fin 4=>x.val) hp)

theorem physical_support_degree {n:Nat} {c:Host} {mark r:Vertex}
 {template:R4333.EdgeColoring (Fin n) (Fin 3)}
 (m:PhysicalNeighborhoodMap c mark (palette 3) template) (hpal:m.colors=foreignEquiv 3)
 (v:Fin n) (hv:m.vertex v=r) (q:Fin 3):
 R4333.colorDegree template q v=
 (attachingSupport c r (palette 3) mark (palette q.castSucc)).card:=by
 rw[←physical_support_image m hpal v hv q,card_image_of_injective _ m.vertex.injective]
 rfl

/-- A four-point foreign support is an actual coloredP4, derived from the
complete marked critical neighborhood. It is not an arbitrary independent4-set.
The host and its palette are never recolored. -/
theorem actual_high_four_support_path (c:Host) (hc:NoMonochromaticTriangle c)
 (r mark:Vertex) (hm:mark∈colorNeighborhood c (palette 3) r)
 (hh:15≤colorDegree c (palette 3) mark) (q:Bool)
 (hs:(attachingSupport c r (palette 3) mark (palette (localColor q).castSucc)).card=4):
 ∃e:Fin 4↪Vertex,
 univ.image e=attachingSupport c r (palette 3) mark (palette (localColor q).castSucc) ∧
 (∀i j:Fin 4,i≠j → (c (e i) (e j)=palette 0 ↔ PathAdjacent i j)):=by
 have hr:r∈colorNeighborhood c (palette 3) mark:=by
  have h:=(mem_colorNeighborhood _ _ _ _).mp hm
  apply (mem_colorNeighborhood _ _ _ _).mpr
  exact ⟨h.1.symm,by rw[c.color_symm];exact h.2⟩
 have hu:=fourColor_colorDegree_le_sixteen c hc (palette 3) mark
 have hcases:colorDegree c (palette 3) mark=15 ∨ colorDegree c (palette 3) mark=16:=by omega
 rcases hcases with h15|h16
 · obtain ⟨t,m,hpal⟩:=physical_k15_fixed_palette c hc mark (palette 3) h15 (foreignEquiv 3)
   obtain ⟨v,hv⟩:=m.covers_neighborhood r hr
   have hd:R4333.colorDegree (R4333.k15Template t) (localColor q) v=4:=by
    rw[physical_support_degree m hpal v hv,hs]
   obtain ⟨hinj,himage,hpath⟩:=template_degree_four_path t v q hd
   let e:Fin 4↪Vertex:=⟨m.vertex ∘ pathOrder t v q,m.vertex.injective.comp hinj⟩
   refine ⟨e,?_,?_⟩
   · change univ.image (m.vertex ∘ pathOrder t v q)=_
     rw[←image_image,himage,physical_support_image m hpal v hv]
   · intro i j hij
     change c (m.vertex (pathOrder t v q i)) (m.vertex (pathOrder t v q j))=palette 0 ↔ _
     rw[m.map_color _ _ (hinj.ne hij),hpal,palette_three]
     have he:(palette ((R4333.k15Template t (pathOrder t v q i) (pathOrder t v q j)).castSucc)=palette 0) ↔
      R4333.k15Template t (pathOrder t v q i) (pathOrder t v q j)=0:=by
       constructor
       · intro hh;apply Fin.ext;exact congrArg (fun x:Fin 4=>x.val) (palette_injective hh)
       · intro hh;rw[hh];rfl
     exact he.trans (hpath i j hij)
 · obtain ⟨t,m,hpal⟩:=physical_k16_fixed_palette c hc mark (palette 3) h16 (foreignEquiv 3)
   obtain ⟨v,hv⟩:=m.covers_neighborhood r hr
   have hd:R4333.colorDegree (R4333.k16Template t) (localColor q) v=4:=by
    rw[physical_support_degree m hpal v hv,hs]
   have hfive:=sixteen_degrees t v q
   omega

#print axioms actual_high_four_support_path
#check actual_high_four_support_path
end PricingC.DegreeFourPath
