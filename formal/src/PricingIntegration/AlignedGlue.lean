import PricingIntegration.AlignedCoordinates
import PricingIntegration.SeedPhysical

namespace PricingIntegration.SeedBinding
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase Ramsey61.CPhysicalNormalization
open PricingC PricingIntegration.SeedCensus PricingG.Completion72

private theorem x_range : ∀ v : Vertex,
    (∃ a : Fin 16, (⟨a.val+1,by omega⟩ : Vertex) = v) ↔ v ∈ rootBlocks 0 := by decide

theorem x_domain (b : Boundary) : scopeDomain (metadata (index b)) 0 = (rootBlocks 0).toFinset := by
  ext v
  simp only [scopeDomain,mem_filter,mem_univ,true_and,x_map_exact,Option.some.injEq,List.mem_toFinset]
  exact x_range v

private theorem y_range : ∀ v : Vertex,
    (17 ≤ v.val ∧ v.val ≤ 32) ↔ v ∈ rootBlocks 1 := by decide

theorem y_domain (b : Boundary) : scopeDomain (metadata (index b)) 2 = (rootBlocks 1).toFinset := by
  ext v
  simp only [scopeDomain,mem_filter,mem_univ,true_and,List.mem_toFinset]
  rw [y_map_complete]
  exact y_range v

theorem rootBlock_saturated (q : Color) : LabelSaturated physicalTag (rootBlocks q).toFinset := by
  intro x hx y hy
  have hcx := (canonicalCell_mem_iff q x).mpr (List.mem_toFinset.mp hx)
  have hcy : canonicalCell y = canonicalCell x := congrArg Prod.fst hy
  exact List.mem_toFinset.mpr ((canonicalCell_mem_iff q y).mp (hcy.trans hcx))

theorem scope_union_domain (m : Metadata) :
    (scopeDomain m 0 ∪ scopeDomain m 2) ∪ scopeDomain m 1 = domain m := by
  ext v
  simp only [scopeDomain,domain,mem_union,mem_filter,mem_univ,true_and]
  constructor
  · rintro ((⟨a,ha⟩ | ⟨a,ha⟩) | ⟨a,ha⟩)
    · exact ⟨0,a,ha⟩
    · exact ⟨2,a,ha⟩
    · exact ⟨1,a,ha⟩
  · rintro ⟨s,a,ha⟩
    have hs : s = 0 ∨ s = 1 ∨ s = 2 := by fin_cases s <;> simp
    rcases hs with rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨a,ha⟩)
    · exact Or.inr ⟨a,ha⟩
    · exact Or.inl (Or.inr ⟨a,ha⟩)

/-- Assemble all three actual scopes into one injective physical map. The
cross-scope injectivity follows from complete root cells and exact overlap
agreement, rather than being supplied as another mathematical premise. -/
theorem aligned_total_map (c : Host) (b : Boundary) (t : AlignedTriple c b)
    (hroot : RootConditions c) :
    ∃ f : Vertex → Vertex, Set.InjOn f (domain (metadata (index b))) ∧
      (∀ s a, f (canonical (metadata (index b)) s a) = actual t s a) ∧
      ∀ v ∈ domain (metadata (index b)), physicalTag (f v) = physicalTag v := by
  let m := metadata (index b)
  let fx := transport m 0 (actualX t)
  let fy := transport m 2 (actualY t)
  let fs := transport m 1 (actualS t)
  have hxy : ∀ x ∈ scopeDomain m 0, x ∈ scopeDomain m 2 → fx x = fy x := by
    intro x hx hy
    obtain ⟨a,ha⟩ := (mem_scopeDomain _ _ _).mp hx
    obtain ⟨d,hd⟩ := (mem_scopeDomain _ _ _).mp hy
    have he : m.maps 0 a.val = m.maps 2 d.val := by
      rw [canonical_some _ _ a,canonical_some _ _ d,ha,hd]
    exact False.elim (xy_disjoint b a.val d.val he)
  have hxs := transported_agreement b 0 1 (actualX t) (actualS t) (actual_xs_agree t)
  have hys := transported_agreement b 2 1 (actualY t) (actualS t) (actual_ys_agree t)
  obtain ⟨f,hf,hfx,hfy,hfs,htags⟩ := glue_three_physical_scopes physicalTag
    (scopeDomain m 0) (scopeDomain m 2) (scopeDomain m 1) fx fy fs
    (by rw [x_domain]; exact rootBlock_saturated 0)
    (by rw [y_domain]; exact rootBlock_saturated 1)
    (transport_injective b 0 (actualX t)) (transport_injective b 2 (actualY t))
    (transport_injective b 1 (actualS t)) hxy hxs hys
    (transport_tags b 0 (actualX t) (actual_tags t hroot 0))
    (transport_tags b 2 (actualY t) (actual_tags t hroot 2))
    (transport_tags b 1 (actualS t) (actual_tags t hroot 1))
  rw [scope_union_domain] at hf htags
  refine ⟨f,hf,?_,htags⟩
  intro s a
  have hmem := (mem_scopeDomain m s (canonical m s a)).mpr ⟨a,rfl⟩
  have hs : s = 0 ∨ s = 1 ∨ s = 2 := by fin_cases s <;> simp
  rcases hs with rfl | rfl | rfl
  · exact (hfx _ hmem).trans (transport_at b 0 (actualX t) a)
  · exact (hfs _ hmem).trans (transport_at b 1 (actualS t) a)
  · exact (hfy _ hmem).trans (transport_at b 2 (actualY t) a)

theorem aligned_triple_supplies_partial_geometry (c : Host) (b : Boundary)
    (t : AlignedTriple c b) (hroot : RootConditions c) :
    Nonempty (PartialGeometry c (metadata (index b))) := by
  obtain ⟨f,hf,hcoords,htags⟩ := aligned_total_map c b t hroot
  let m := metadata (index b)
  have coordImage : ∀ s a u, m.maps s a = some u →
      ∃ d : Present m s, d.val = a ∧ canonical m s d = u := by
    intro s a u h
    exact ⟨⟨a,by simp [h]⟩,rfl,by simp [canonical,h]⟩
  refine ⟨⟨(fun v => f v.val),?_,(fun v => htags v.val v.property),?_,?_,?_⟩⟩
  · intro u v h
    exact Subtype.ext (hf u.property v.property h)
  · intro s a d u v hu hv hne
    obtain ⟨aa,haa,hua⟩ := coordImage s a u hu
    obtain ⟨dd,hdd,hvd⟩ := coordImage s d v hv
    have had : aa ≠ dd := by intro h; exact hne (hua.symm.trans ((congrArg (canonical m s) h).trans hvd))
    have hfu : f u = actual t s aa := by rw [←hua]; exact hcoords s aa
    have hfv : f v = actual t s dd := by rw [←hvd]; exact hcoords s dd
    change c (f u) (f v) = _
    rw [hfu,hfv]
    have hc := actual_colors t s aa dd had
    simpa only [haa,hdd] using hc
  · intro v hv
    obtain ⟨a,ha⟩ := (mem_filter.mp hv).2
    obtain ⟨aa,haa,hua⟩ := coordImage 1 a v ha
    change f v ∈ colorNeighborhood c (palette 2) 33
    rw [←hua,hcoords 1 aa]
    exact t.xs.physical.s.mem_scope ⟨aa.val,sPresent t aa⟩
  · intro v hv
    obtain ⟨a,ha⟩ := t.xs.physical.s.covers v hv
    have hp : (m.maps 1 a.val).isSome = true :=
      (s_present_exact b a.val).mpr ((t.xs.present_match a.val).mp a.property)
    let aa : Present m 1 := ⟨a.val,hp⟩
    let u := canonical m 1 aa
    have hu : u ∈ physicalS m := mem_filter.mpr ⟨mem_univ _,a.val,canonical_some m 1 aa⟩
    refine ⟨u,hu,?_⟩
    change f u = v
    rw [hcoords 1 aa]
    exact ha

#print axioms aligned_triple_supplies_partial_geometry
end PricingIntegration.SeedBinding
