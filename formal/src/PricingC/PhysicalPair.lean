import PricingC.ReferenceScopes

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase Ramsey61.CAnchorGeometry PairTables

structure PhysicalXSPair (c : Host) where
  pair : Fin 6
  x : ReferenceScope c 0 (palette 0) paletteX (representativeX pair)
  s : ReferenceScope c 33 (palette 2) paletteS (representativeS pair)
  x_full : x.present = univ
  root_present : (0 : Fin 16) ∈ s.present
  root_image : s.vertex ⟨0,root_present⟩ = 0
  anchor : Fin 5 ↪ Vertex
  anchor_range : univ.image anchor = anchorSupport c 0
  x_anchor_present : ∀ j, generators j ∈ x.present
  s_anchor_present : ∀ j, generators j ∈ s.present
  x_anchor_image : ∀ j, x.vertex ⟨generators j,x_anchor_present j⟩ = anchor j
  s_anchor_image : ∀ j, s.vertex ⟨generators j,s_anchor_present j⟩ = anchor j

/-- Actual normalized C geometry supplies an exact simultaneous X/S reference
pair with all physical overlaps and S's actual root retained. -/
theorem actual_C_supplies_XS_pair (c : Host) (hc : NoMonochromaticTriangle c)
    (hroot : RootConditions c) (hmarked : 15 ≤ colorDegree c (palette 2) 33)
    (hshape : ThreeAnchorShapes c) : Nonempty (PhysicalXSPair c) := by
  classical
  have hxdeg : colorDegree c (palette 0) 0 = 16 := by simpa using normalized_root_degree c hroot 0
  obtain ⟨tx,⟨fx⟩⟩ := fixed_palette_k16 c hc 0 (palette 0) hxdeg paletteX
  let mx := completed_from_k16 c 0 (palette 0) paletteX tx fx
  obtain ⟨ms⟩ := high_neighborhood_completion c hc 33 (palette 2) hmarked paletteS
  let A := anchorSupport c 0
  have hA : A.card = 5 := hshape.1
  let ord := finiteFiveOrder A hA
  let phys : Fin 5 ↪ Vertex := ord.toEmbedding.trans (Function.Embedding.subtype _)
  have hmX : ∀ j, phys j ∈ colorNeighborhood c (palette 0) 0 := fun j => (mem_inter.mp (ord j).property).2
  have hmS : ∀ j, phys j ∈ colorNeighborhood c (palette 2) 33 := fun j => (mem_inter.mp (ord j).property).1
  let ax := liftPhysicalAnchor mx phys hmX
  let as := liftPhysicalAnchor ms phys hmS
  have hvx : ∀ j, mx.vertex (ax j) = phys j := liftPhysicalAnchor_val mx phys hmX
  have hvs : ∀ j, ms.vertex (as j) = phys j := liftPhysicalAnchor_val ms phys hmS
  have hix : R4333.IsColorIndependentSet mx.model 0 (referenceAnchor mx ax) := by
    apply referenceAnchor_independent mx ax 0
    intro i j hij
    rw [hvx i,hvx j,paletteX_zero]
    exact neighborhood_pair_avoids c hc 33 (palette 2) _ _ (hmS i) (hmS j) (phys.injective.ne hij)
  let rs := ms.scopeEquiv.symm ⟨0,root_in_marked_scope c hroot⟩
  have hrs : ms.vertex rs = 0 := ms.scopeEquiv_symm_val _
  have haS : ∀ j, ms.vertex (as j) ∈ colorNeighborhood c (palette 0) 0 := by
    intro j; rw [hvs j]; exact hmX j
  have hcenter := full_anchor_root_center c hroot ms as haS rs hrs
  have hagree : ∀ j, mx.vertex (ax j) = ms.vertex (as j) := fun j => (hvx j).trans (hvs j).symm
  obtain ⟨k,ex,es,order,hes0,hanchors,hxc,hsc⟩ :=
    paired_scopes_six_orbits mx ms ax as hagree hix rs.val hcenter paletteXS_cycle
  let x := referenceScope mx (representativeX k) ex hxc
  let s := referenceScope ms (representativeS k) es hsc
  let anchor := order.trans phys
  have hxfull : x.present = univ := referenceScope_full mx _ ex hxc rfl
  have hsp : (0 : Fin 16) ∈ s.present := by
    change 0 ∈ univ.filter (fun v => es v ∈ ms.present)
    simp only [mem_filter,mem_univ,true_and,hes0]
    exact rs.property
  have hsroot : s.vertex ⟨0,hsp⟩ = 0 := by
    change ms.vertex ⟨es 0,_⟩ = 0
    simpa only [hes0] using hrs
  have hxap : ∀ j, generators j ∈ x.present := by intro j; rw [hxfull]; exact mem_univ _
  have hsap : ∀ j, generators j ∈ s.present := by
    intro j
    change generators j ∈ univ.filter (fun v => es v ∈ ms.present)
    simp only [mem_filter,mem_univ,true_and,(hanchors j).2]
    exact (as (order j)).property
  have hxa : ∀ j, x.vertex ⟨generators j,hxap j⟩ = anchor j := by
    intro j
    change mx.vertex ⟨ex (generators j),_⟩ = phys (order j)
    apply Eq.trans ?_ (hvx (order j))
    apply congrArg mx.vertex
    exact Subtype.ext (hanchors j).1
  have hsa : ∀ j, s.vertex ⟨generators j,hsap j⟩ = anchor j := by
    intro j
    change ms.vertex ⟨es (generators j),_⟩ = phys (order j)
    apply Eq.trans ?_ (hvs (order j))
    apply congrArg ms.vertex
    exact Subtype.ext (hanchors j).2
  have harange : univ.image anchor = A := by
    ext v
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨j,rfl⟩; exact (ord (order j)).property
    · intro hv
      obtain ⟨j,hj⟩ := Finite.surjective_of_injective order.injective (ord.symm ⟨v,hv⟩)
      refine ⟨j,?_⟩
      change (ord (order j)).val = v
      rw [hj,Equiv.apply_symm_apply]
  exact ⟨⟨k,x,s,hxfull,hsp,hsroot,anchor,harange,hxap,hsap,hxa,hsa⟩⟩

#print axioms actual_C_supplies_XS_pair
end PricingC
