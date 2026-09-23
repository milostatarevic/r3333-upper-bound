import PricingG.CoreRealization
import PricingC.GCaseCore

namespace PricingG
open Ramsey61 Ramsey61.CEncodingCore PricingC PricingC.GIsomorphic PricingC.AdjacentAutomorphisms
open PricingIntegration.CoreLayout PricingIntegration.LocalRelations

@[simp] theorem blockPoint_coreX (i : Fin 16) : blockPoint (coreX i) = i := by
  apply Fin.ext; dsimp [blockPoint,coreX]; omega
@[simp] theorem blockPoint_coreY (i : Fin 16) : blockPoint (coreY i) = i := by
  apply Fin.ext; dsimp [blockPoint,coreY]; omega

@[simp] theorem iso_base_0X (k y g i) : baseCore k y g 0 (coreX i) = some 0 := by
  simp [baseCore,coreX,Ne.symm (coreX_ne_zero i)]; omega
@[simp] theorem iso_base_X0 (k y g i) : baseCore k y g (coreX i) 0 = some 0 := by
  simp [baseCore,coreX]; omega
@[simp] theorem iso_base_0Y (k y g i) : baseCore k y g 0 (coreY i) = some 1 := by
  simp [baseCore,coreY,Ne.symm (coreY_ne_zero i)]; omega
@[simp] theorem iso_base_Y0 (k y g i) : baseCore k y g (coreY i) 0 = some 1 := by
  simp [baseCore,coreY]; omega
@[simp] theorem iso_base_XX (k y g) (i j : Fin 16) (hij : i ≠ j) :
    baseCore k y g (coreX i) (coreX j) = some (xPalette (rootColor k i j)) := by
  have hi : (coreX i).val ≤ 16 := by dsimp [coreX]; omega
  have hj : (coreX j).val ≤ 16 := by dsimp [coreX]; omega
  simp [baseCore,hi,hj,hij]
@[simp] theorem iso_base_YY (k y g) (i j : Fin 16) (hij : i ≠ j) :
    baseCore k y g (coreY i) (coreY j) = some (yPalette (nativeColor y i j)) := by
  have hi : ¬(coreY i).val ≤ 16 := by dsimp [coreY]; omega
  have hj : ¬(coreY j).val ≤ 16 := by dsimp [coreY]; omega
  simp [baseCore,hi,hj,hij]
@[simp] theorem iso_base_XY (k y g i j) :
    baseCore k y g (coreX i) (coreY j) = crossColor g i j := by
  have hi : (coreX i).val ≤ 16 := by dsimp [coreX]; omega
  have hj : ¬(coreY j).val ≤ 16 := by dsimp [coreY]; omega
  simp [baseCore,hi,hj]
@[simp] theorem iso_base_YX (k y g i j) :
    baseCore k y g (coreY j) (coreX i) = crossColor g i j := by
  have hi : (coreX i).val ≤ 16 := by dsimp [coreX]; omega
  have hj : ¬(coreY j).val ≤ 16 := by dsimp [coreY]; omega
  simp [baseCore,hi,hj,Ne.symm (coreX_ne_Y i j)]

abbrev CanonicalModel (c : Host) (r : Vertex) :=
  GuardedGraphModel c r (palette 0) (palette 1) (by decide)

noncomputable def physicalCoordinate {c r p} (b : PhysicalBlock c r p)
    (e : Equiv.Perm (Fin 16)) : Fin 16 ↪ Vertex := e.toEmbedding.trans b.map.vertex

/-- Exact physical 3600-case entrance. The root, both physical16blocks,
all low-color data and one global palette remain compatible. -/
theorem isomorphic_core_realized (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hG : RegularOverlapGuard c r (palette 0) (palette 1))
    (m : CanonicalModel c r) (hz : defectCount m.K m.J = 0) :
    ∃ (kind : Fin 2) (y : Fin 72) (g : Fin 25) (phys : Fin 33 ↪ Vertex),
      Realizes c phys (baseCore kind y g) ∧
      (∀ i, 15 ≤ colorDegree c (palette 1) (phys (coreX i))) ∧
      (∀ i, 15 ≤ colorDegree c (palette 0) (phys (coreY i))) := by
  classical
  have heq : m.K = m.J := zero_defects_graph_eq _ _ m.K_srg m.J_srg
    (GraphRootedDichotomy.unrooted (m.shared_graph_rooted_dichotomy hc hG)) hz
  obtain ⟨e,kind,hX⟩ := m.X.physical_root_normalized (palette 1) (by decide) (scopePalette true) rfl
  obtain ⟨gi,hgi⟩ := m.zero_defects_exact25_coordinates hc hG hz e
  let fI := m.firstCenterIso hc hG heq
  let eY : xorGraph ≃g (m.Y.graph (palette 0) (by decide)) := e.trans fI.symm
  obtain ⟨j,hY⟩ := m.Y.coordinateColoring_exact72 (palette 0) (by decide) (scopePalette false) rfl eY
  obtain ⟨yi,hyi⟩ := censusRow_bijective.2 j
  rw [←hyi] at hY
  let X := physicalCoordinate m.X e.toEquiv
  let Y := physicalCoordinate m.Y eY.toEquiv
  have hXm : ∀ i, X i ∈ colorNeighborhood c (palette 0) r := fun i => m.X.map.mem_neighborhood (e i)
  have hYm : ∀ i, Y i ∈ colorNeighborhood c (palette 1) r := fun i => m.Y.map.mem_neighborhood (eY i)
  let phys := coreEmbedding c r X Y hXm hYm
  have eMap (x y : Fin 16) : m.K.Adj (e x) (e y) ↔ xorGraph.Adj x y := e.map_rel_iff
  have hmap (x : Fin 16) : m.imageRule (e x) = e (retainedMap gi x) := by
    calc
      m.imageRule (e x) = e (e.symm (m.imageRule (e x))) := (e.apply_symm_apply _).symm
      _ = e (retainedMap gi x) := congrArg e (hgi x)
  have cross1 (x y : Fin 16) : c (X x) (Y y) = palette 1 ↔ Completion72.xorClebsch x y = true := by
    have hh := m.first_fiber (e x) (m.f.symm (e y))
    change m.K.Adj (m.f (m.f.symm (e y))) (e x) ↔ c (X x) (Y y) = palette 1 at hh
    rw [m.f.apply_symm_apply,eMap,xorGraph.adj_comm] at hh
    exact hh.symm.trans ((show ∀ x y, xorGraph.Adj x y ↔ Completion72.xorClebsch x y = true from by decide) x y)
  have cross0 (x y : Fin 16) : c (X x) (Y y) = palette 0 ↔
      Completion72.xorClebsch (retainedMap gi x) y = true := by
    have hh : c (X x) (Y y) = palette 0 ↔ m.K.Adj (m.imageRule (e x)) (e y) := by
      constructor
      · intro h
        have hk := fI.map_rel_iff.mpr ((m.second_fiber (e x) (m.f.symm (e y))).mpr h)
        change m.K.Adj (m.imageRule (e x)) (m.f (m.f.symm (e y))) at hk
        simpa only [m.f.apply_symm_apply] using hk
      · intro h
        apply (m.second_fiber (e x) (m.f.symm (e y))).mp
        apply fI.map_rel_iff.mp
        change m.K.Adj (m.imageRule (e x)) (m.f (m.f.symm (e y)))
        simpa only [m.f.apply_symm_apply] using h
    rw [hh,hmap,eMap]
    exact (show ∀ x y, xorGraph.Adj x y ↔ Completion72.xorClebsch x y = true from by decide) _ _
  refine ⟨kind,yi,gi,phys,?_,?_,?_⟩
  · apply realizes_from_blocks c r X Y hXm hYm (baseCore kind yi gi)
      (fun i j => xPalette (rootColor kind i j)) (fun i j => yPalette (nativeColor yi i j))
      (iso_base_0X kind yi gi) (iso_base_X0 kind yi gi)
      (iso_base_0Y kind yi gi) (iso_base_Y0 kind yi gi)
      (iso_base_XX kind yi gi) (iso_base_YY kind yi gi)
    · intro i j; rw [iso_base_YX,iso_base_XY]
    · intro i j hij; exact hX i j hij
    · intro i j hij; exact hY i j hij
    · intro i j
      rw [iso_base_XY]
      by_cases h1 : Completion72.xorClebsch i j = true
      · exact ⟨1,by simp [crossColor,h1,Allows],(cross1 i j).mpr h1⟩
      · by_cases h0 : Completion72.xorClebsch (retainedMap gi i) j = true
        · exact ⟨0,by simp [crossColor,h1,h0,Allows],(cross0 i j).mpr h0⟩
        · rcases low_color_of_not_high (c (X i) (Y j))
            (fun h => h0 ((cross0 i j).mp h)) (fun h => h1 ((cross1 i j).mp h)) with h | h
          · exact ⟨2,by simp [crossColor,h1,h0,Allows],h⟩
          · exact ⟨3,by simp [crossColor,h1,h0,Allows],h⟩
  · intro i
    change 15 ≤ colorDegree c _ (coreEmbedding c r X Y hXm hYm (coreX i))
    rw [coreEmbedding_X]
    exact hG.first_opposite_high _ (hXm i)
  · intro i
    change 15 ≤ colorDegree c _ (coreEmbedding c r X Y hXm hYm (coreY i))
    rw [coreEmbedding_Y]
    exact hG.second_opposite_high _ (hYm i)

#print axioms isomorphic_core_realized
end PricingG
