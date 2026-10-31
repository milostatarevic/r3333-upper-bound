import UniformK60.HostNormalizationEntrance
import UniformK60.CEntranceCanonical
import UniformK60.PhysicalTypeTransport

set_option autoImplicit false
namespace UniformK60.CEntranceBlocks
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette
open UniformK60.ClassificationGeometry UniformK60.PhysicalHelpers
open UniformK60.CommonBlocks UniformK60.CommonEntrance
open UniformK60.CommonExchange UniformK60.CEntranceSource
open PricingABD.ABLayout PricingABD.ABGeometry

private theorem swap_pal12 (a : Fin 3) :
    colorSwap.symm (foreignEquiv 2 a).val=(foreignEquiv 1 a).val := by
  fin_cases a <;> rfl

private theorem swap_pal21 (a : Fin 3) :
    colorSwap.symm (foreignEquiv 1 a).val=(foreignEquiv 2 a).val := by
  fin_cases a <;> rfl

/-- The same complete critical cell after the global foreign-color exchange. -/
noncomputable def swapLeft {n : Nat} {c : Host} {r : Vertex}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette 2) t)
    (hp : m.colors=foreignEquiv 2) :
    PhysicalNeighborhoodMap (swappedHost c) r (palette 1) t where
  vertex := m.vertex
  mem_neighborhood i := (swappedHost_mem _ _ _ _).mpr (m.mem_neighborhood i)
  covers_neighborhood v hv := m.covers_neighborhood v ((swappedHost_mem _ _ _ _).mp hv)
  colors := foreignEquiv 1
  map_color a b hab := by
    change colorSwap.symm (c (m.vertex a) (m.vertex b))=_
    rw [m.map_color a b hab,hp,swap_pal12]

noncomputable def swapRight {n : Nat} {c : Host} {r : Vertex}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r (palette 1) t)
    (hp : m.colors=foreignEquiv 1) :
    PhysicalNeighborhoodMap (swappedHost c) r (palette 2) t where
  vertex := m.vertex
  mem_neighborhood i := (swappedHost_mem _ _ _ _).mpr (m.mem_neighborhood i)
  covers_neighborhood v hv := m.covers_neighborhood v ((swappedHost_mem _ _ _ _).mp hv)
  colors := foreignEquiv 2
  map_color a b hab := by
    change colorSwap.symm (c (m.vertex a) (m.vertex b))=_
    rw [m.map_color a b hab,hp,swap_pal21]

private theorem assemble (c : Host) (hc : NoMonochromaticTriangle c)
    (profile : Profile) (types : Types) (r mark : Vertex)
    (left : PhysicalNeighborhoodMap c r (palette 1) (model (leftLarge ⟨profile,false⟩) types.left))
    (right : PhysicalNeighborhoodMap c r (palette 2) (model (rightLarge ⟨profile,false⟩) types.right))
    (hl : left.colors=foreignEquiv 1) (hr : right.colors=foreignEquiv 2)
    (hm : mark∈colorNeighborhood c (palette 3) r)
    (hh : 15≤colorDegree c (palette 3) mark)
    (ho : ∀ five,CompletionC.CommonCases.NativeOwner ⟨profile,five⟩ types) :
    ∃ five : Bool,∃ b : Blocks c ⟨profile,five⟩ types,
      CompletionC.CommonCases.NativeOwner ⟨profile,five⟩ types ∧ b.root=r ∧ b.mark=mark := by
  rcases low_support_four_or_five c hc r mark hm hh with hs|hs
  · exact ⟨false,of_cells _ _ r mark left right hl hr hm hh hs,ho false,rfl,rfl⟩
  · exact ⟨true,of_cells _ _ r mark left right hl hr hm hh hs,ho true,rfl,rfl⟩

private theorem canonical_B (c : Host) (hc : NoMonochromaticTriangle c)
    (r mark : Vertex)
    (hd : ∀ q : Color,colorDegree c (palette q) r=CEntranceLayout.shape 2 q)
    (hm : mark∈colorNeighborhood c (palette 3) r)
    (hh : 15≤colorDegree c (palette 3) mark) :
    ∃ five : Bool,∃ types : Types,∃ b : Blocks c (CEntranceCanonical.layout 2 five) types,
      CompletionC.CommonCases.NativeOwner (CEntranceCanonical.layout 2 five) types ∧
      b.root=r ∧ b.mark=mark := by
  obtain ⟨lt,left,hl⟩ := physical_k15_fixed_palette c hc r (palette 1) (hd 1) (foreignEquiv 1)
  obtain ⟨rt,right,hr⟩ := physical_k16_fixed_palette c hc r (palette 2) (hd 2) (foreignEquiv 2)
  obtain ⟨five,b,ho,hroot,hmark⟩ := assemble c hc .B ⟨lt,rt,true⟩ r mark left right hl hr hm hh
    (by intro five;cases rt <;> simp [CompletionC.CommonCases.NativeOwner])
  exact ⟨five,⟨lt,rt,true⟩,b,ho,hroot,hmark⟩

private theorem canonical_A (c : Host) (hc : NoMonochromaticTriangle c)
    (r mark : Vertex) (mode : Mode) (hne : mode≠2)
    (hd : ∀ q : Color,colorDegree c (palette q) r=CEntranceLayout.shape mode q)
    (hm : mark∈colorNeighborhood c (palette 3) r)
    (hh : 15≤colorDegree c (palette 3) mark) :
    ∃ σ : FourColor ≃ FourColor,let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧
      (∀ q : Color,colorDegree d (palette q) r=CEntranceLayout.shape mode q) ∧
      ∃ five : Bool,∃ types : Types,∃ b : Blocks d (CEntranceCanonical.layout mode five) types,
        CompletionC.CommonCases.NativeOwner (CEntranceCanonical.layout mode five) types ∧
        b.root=r ∧ b.mark=mark := by
  have h1 : colorDegree c (palette 1) r=16 := by
    rw [hd];fin_cases mode <;> simp_all [CEntranceLayout.shape]
  have h2 : colorDegree c (palette 2) r=16 := by
    rw [hd];fin_cases mode <;> rfl
  have layout_eq : ∀ five,CEntranceCanonical.layout mode five=⟨.A,five⟩ := by
    intro five;simp only [CEntranceCanonical.layout,if_neg hne]
  obtain ⟨lt,left,hl⟩ := physical_k16_fixed_palette c hc r (palette 1) h1 (foreignEquiv 1)
  obtain ⟨rt,right,hr⟩ := physical_k16_fixed_palette c hc r (palette 2) h2 (foreignEquiv 2)
  by_cases ho : lt=false ∨ rt=true
  · obtain ⟨five,b,howner,hroot,hmark⟩ := assemble c hc .A ⟨lt,rt,true⟩ r mark left right hl hr hm hh
      (by intro five;exact ⟨ho,Or.inr rfl⟩)
    refine ⟨Equiv.refl _,hc,hd,five,⟨lt,rt,true⟩,?_⟩
    rw [layout_eq five]
    exact ⟨b,howner,hroot,hmark⟩
  · have hlt : lt=true := by cases lt <;> simp_all
    have hrt : rt=false := by cases rt <;> simp_all
    have hgood := swappedHost_good c hc
    have hm' : mark∈colorNeighborhood (swappedHost c) (palette 3) r :=
      (swappedHost_mem _ _ _ _).mpr hm
    have hh' : 15≤colorDegree (swappedHost c) (palette 3) mark := by
      change 15≤colorDegree (relabel c (Equiv.refl _) colorSwap) (palette 3) mark
      rw [relabel_degree];exact hh
    have hd' : ∀ q : Color,colorDegree (swappedHost c) (palette q) r=CEntranceLayout.shape mode q := by
      intro q
      change colorDegree (relabel c (Equiv.refl _) colorSwap) (palette q) r=_
      rw [relabel_degree]
      fin_cases q
      · exact hd 0
      · change colorDegree c (palette 2) r=_
        rw [hd];fin_cases mode <;> simp_all [CEntranceLayout.shape]
      · change colorDegree c (palette 1) r=_
        rw [hd];fin_cases mode <;> simp_all [CEntranceLayout.shape]
      · exact hd 3
    obtain ⟨five,b,howner,hroot,hmark⟩ := assemble (swappedHost c) hgood .A ⟨rt,lt,true⟩ r mark
      (swapLeft right hr) (swapRight left hl) rfl rfl hm' hh'
      (by intro five;exact ⟨Or.inl hrt,Or.inr rfl⟩)
    refine ⟨colorSwap,hgood,hd',five,⟨rt,lt,true⟩,?_⟩
    rw [layout_eq five]
    exact ⟨b,howner,hroot,hmark⟩

/-- Every exterior C ticket supplies the actual common support-word input.
Only the two foreign cells are classified. The marked type is a census tag;
there is no template hypothesis on its13- or14-vertex root cell. -/
theorem actual_blocks_of_entrance (c : Host) (hc : NoMonochromaticTriangle c)
    (hw : CEntranceWitness c) :
    ∃ σ : FourColor ≃ FourColor,∃ root mark : Vertex,∃ mode : Mode,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧
      (∀ q : Color,colorDegree d (palette q) root=CEntranceLayout.shape mode q) ∧
      ∃ five : Bool,∃ types : Types,∃ b : Blocks d (CEntranceCanonical.layout mode five) types,
        CompletionC.CommonCases.NativeOwner (CEntranceCanonical.layout mode five) types ∧
        b.root=root ∧ b.mark=mark := by
  obtain ⟨root,mark,c1,orientation,σ,good,hd,hm,hh⟩ :=
    CEntranceExtraction.of_entrance_witness c hc hw
  let d := relabel c (Equiv.refl _) σ
  cases c1
  · cases orientation
    · obtain ⟨five,types,b,ho,hr,hmark⟩ := canonical_B d good root mark hd hm hh
      exact ⟨σ,root,mark,2,good,hd,five,types,b,ho,hr,hmark⟩
    · have good' := swappedHost_good d good
      have hd' : ∀ q : Color,colorDegree (swappedHost d) (palette q) root=CEntranceLayout.shape 2 q := by
        intro q
        change colorDegree (relabel d (Equiv.refl _) colorSwap) (palette q) root=_
        rw [relabel_degree]
        fin_cases q
        · exact hd 0
        · exact hd 2
        · exact hd 1
        · exact hd 3
      have hm' : mark∈colorNeighborhood (swappedHost d) (palette 3) root :=
        (swappedHost_mem _ _ _ _).mpr hm
      have hh' : 15≤colorDegree (swappedHost d) (palette 3) mark := by
        change 15≤colorDegree (relabel d (Equiv.refl _) colorSwap) (palette 3) mark
        rw [relabel_degree];exact hh
      obtain ⟨five,types,b,ho,hr,hmark⟩ := canonical_B (swappedHost d) good' root mark hd' hm' hh'
      exact ⟨colorSwap.trans σ,root,mark,2,good',hd',five,types,b,ho,hr,hmark⟩
  · cases orientation
    · obtain ⟨τ,good',hd',five,types,b,ho,hr,hmark⟩ := canonical_A d good root mark 0 (by decide) hd hm hh
      exact ⟨τ.trans σ,root,mark,0,good',hd',five,types,b,ho,hr,hmark⟩
    · obtain ⟨τ,good',hd',five,types,b,ho,hr,hmark⟩ := canonical_A d good root mark 1 (by decide) hd hm hh
      exact ⟨τ.trans σ,root,mark,1,good',hd',five,types,b,ho,hr,hmark⟩

/-- Preserve the selector's eligible-witness interface. -/
theorem actual_blocks (c : Host) (hc : NoMonochromaticTriangle c) (hw : CExteriorWitness c) :
    ∃ σ : FourColor ≃ FourColor,∃ root mark : Vertex,∃ mode : Mode,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧
      (∀ q : Color,colorDegree d (palette q) root=CEntranceLayout.shape mode q) ∧
      ∃ five : Bool,∃ types : Types,∃ b : Blocks d (CEntranceCanonical.layout mode five) types,
        CompletionC.CommonCases.NativeOwner (CEntranceCanonical.layout mode five) types ∧
        b.root=root ∧ b.mark=mark :=
  actual_blocks_of_entrance c hc (exterior_is_entrance c hw)

#print axioms actual_blocks_of_entrance
#print axioms actual_blocks
end UniformK60.CEntranceBlocks
