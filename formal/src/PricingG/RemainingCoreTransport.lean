import PricingG.IsomorphicCoreTransport
import PricingIntegration.RemainingGCore

namespace PricingG
open Ramsey61 Ramsey61.CEncodingCore PricingC
open PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore

@[simp] theorem remaining_view_X (i : Fin 16) : view (coreX i) = some (false,i) := by
  have he : coreX i = xVertex i := by apply Fin.ext; dsimp [coreX,xVertex]; omega
  rw [he,view_x]
@[simp] theorem remaining_view_Y (i : Fin 16) : view (coreY i) = some (true,i) := by
  have he : coreY i = yVertex i := by apply Fin.ext; dsimp [coreY,yVertex]; omega
  rw [he,view_y]

@[simp] theorem rem_base_0X (k d y i) : base k d y 0 (coreX i) = some 0 := by simp [base,view_root,Ne.symm (coreX_ne_zero i)]
@[simp] theorem rem_base_X0 (k d y i) : base k d y (coreX i) 0 = some 0 := by simp [base,view_root]
@[simp] theorem rem_base_0Y (k d y i) : base k d y 0 (coreY i) = some 1 := by simp [base,view_root,Ne.symm (coreY_ne_zero i)]
@[simp] theorem rem_base_Y0 (k d y i) : base k d y (coreY i) 0 = some 1 := by simp [base,view_root]
@[simp] theorem rem_base_XX (k d y) (i j : Fin 16) (hij : i ≠ j) :
    base k d y (coreX i) (coreX j) = some (xColors (rootColor k i j)) := by simp [base,hij]
@[simp] theorem rem_base_YY (k d y) (i j : Fin 16) (hij : i ≠ j) :
    base k d y (coreY i) (coreY j) =
      some (yColors (nativeColor y ((decompEquiv d).symm i) ((decompEquiv d).symm j))) := by simp [base,hij]
@[simp] theorem rem_base_XY (k d y i j) : base k d y (coreX i) (coreY j) = cross d i j := by simp [base]
@[simp] theorem rem_base_YX (k d y i j) : base k d y (coreY j) (coreX i) = cross d i j := by simp [base,Ne.symm (coreX_ne_Y i j)]

theorem native_diagonal_not_one (d : Fin 72) (u : Fin 16) : nativeColor d u u ≠ 1 := by
  intro h
  have h' : nativeColor d (decompEquiv d ((decompEquiv d).symm u))
      (decompEquiv d ((decompEquiv d).symm u)) = 1 := by simpa only [Equiv.apply_symm_apply] using h
  exact xorGraph.loopless.irrefl _ ((decomp_graph d _ _).mp h')

/-- The diagonal full-defect endpoint enters the exact10368 retained cores.
The canonical-to-physical map of the second Clebsch color is applied in its
recorded direction, and both low colors stay globally fixed. -/
theorem remaining_core_realized (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hG : RegularOverlapGuard c r (palette 0) (palette 1))
    (m : CanonicalModel c r) (hz : defectCount m.K m.J = 16) :
    ∃ (kind : Fin 2) (d y : Fin 72) (phys : Fin 33 ↪ Vertex),
      Realizes c phys (base kind d y) ∧
      (∀ i, 15 ≤ colorDegree c (palette 1) (phys (coreX i))) ∧
      (∀ i, 15 ≤ colorDegree c (palette 0) (phys (coreY i))) := by
  classical
  have hd : GraphRootedDichotomy m.K m.J m.imageRule := m.shared_graph_rooted_dichotomy hc hG
  have hid := full_defects_image_identity m.K m.J m.K_srg m.J_srg m.imageRule hd hz
  have hdis := full_defects_disjoint m.K m.J m.K_srg m.J_srg hd.unrooted hz
  obtain ⟨e,kind,hX⟩ := m.X.physical_root_normalized (palette 1) (by decide) (scopePalette true) rfl
  have eMap (x y : Fin 16) : m.K.Adj (e x) (e y) ↔ xorGraph.Adj x y := e.map_rel_iff
  obtain ⟨di0,hD⟩ := full_defects_exact72_coordinates m.K m.J m.K_srg m.J_srg m.imageRule hd hz e
  obtain ⟨di,hdi⟩ := GIsomorphic.censusRow_bijective.2 di0
  rw [←hdi] at hD
  have jMap (x y : Fin 16) : m.J.Adj (e x) (e y) ↔ nativeColor di x y = 1 := by
    by_cases hxy : x = y
    · subst y; simp [native_diagonal_not_one]
    · have hh := decomposition_one_iff m.K m.J hdis (e x) (e y)
      exact hh.symm.trans (Iff.of_eq (congrArg (fun a : Fin 3 => a = 1) (hD x y hxy)))
  let eY : xorGraph ≃g (m.Y.graph (palette 0) (by decide)) :=
    { toEquiv := (decompEquiv di).trans (e.toEquiv.trans m.g)
      map_rel_iff' := by
        intro x y
        change (m.Y.graph (palette 0) _).Adj (m.g (e (decompEquiv di x))) (m.g (e (decompEquiv di y))) ↔ _
        exact (m.J_iff _ _).symm.trans ((jMap _ _).trans (decomp_graph di x y)) }
  obtain ⟨yi0,hY0⟩ := m.Y.coordinateColoring_exact72 (palette 0) (by decide) (scopePalette false) rfl eY
  obtain ⟨yi,hyi⟩ := GIsomorphic.censusRow_bijective.2 yi0
  rw [←hyi] at hY0
  let X := physicalCoordinate m.X e.toEquiv
  let Y := physicalCoordinate m.Y (e.toEquiv.trans m.g)
  have hXm : ∀ i, X i ∈ colorNeighborhood c (palette 0) r := fun i => m.X.map.mem_neighborhood (e i)
  have hYm : ∀ i, Y i ∈ colorNeighborhood c (palette 1) r := fun i => m.Y.map.mem_neighborhood (m.g (e i))
  let phys := coreEmbedding c r X Y hXm hYm
  have hY (x y : Fin 16) (hxy : x ≠ y) : c (Y x) (Y y) =
      palette (yColors (nativeColor yi ((decompEquiv di).symm x) ((decompEquiv di).symm y))) := by
    have hh := hY0 ((decompEquiv di).symm x) ((decompEquiv di).symm y)
      ((decompEquiv di).symm.injective.ne hxy)
    change c (m.Y.map.vertex (m.g (e (decompEquiv di ((decompEquiv di).symm x)))))
      (m.Y.map.vertex (m.g (e (decompEquiv di ((decompEquiv di).symm y))))) = _ at hh
    simp only [Equiv.apply_symm_apply] at hh
    exact hh
  have cross1 (x y : Fin 16) : c (X x) (Y y) = palette 1 ↔ xorGraph.Adj x y := by
    have hh := m.first_fiber (e x) (m.g (e y))
    change m.K.Adj (m.imageRule (e y)) (e x) ↔ c (X x) (Y y) = palette 1 at hh
    rw [hid,eMap,xorGraph.adj_comm] at hh
    exact hh.symm
  have cross0 (x y : Fin 16) : c (X x) (Y y) = palette 0 ↔ nativeColor di x y = 1 :=
    (m.J_physical_iff (e x) (e y)).symm.trans (jMap x y)
  refine ⟨kind,di,yi,phys,?_,?_,?_⟩
  · apply realizes_from_blocks c r X Y hXm hYm (base kind di yi)
      (fun i j => xColors (rootColor kind i j))
      (fun i j => yColors (nativeColor yi ((decompEquiv di).symm i) ((decompEquiv di).symm j)))
      (rem_base_0X kind di yi) (rem_base_X0 kind di yi)
      (rem_base_0Y kind di yi) (rem_base_Y0 kind di yi)
      (rem_base_XX kind di yi) (rem_base_YY kind di yi)
    · intro i j; rw [rem_base_YX,rem_base_XY]
    · intro i j hij; exact hX i j hij
    · exact hY
    · intro i j
      rw [rem_base_XY]
      by_cases h1 : xorGraph.Adj i j
      · exact ⟨1,by simp [cross,h1,Allows],(cross1 i j).mpr h1⟩
      · by_cases h0 : nativeColor di i j = 1
        · exact ⟨0,by simp [cross,h1,h0,Allows],(cross0 i j).mpr h0⟩
        · rcases low_color_of_not_high (c (X i) (Y j))
            (fun h => h0 ((cross0 i j).mp h)) (fun h => h1 ((cross1 i j).mp h)) with h | h
          · exact ⟨2,by simp [cross,h1,h0,Allows],h⟩
          · exact ⟨3,by simp [cross,h1,h0,Allows],h⟩
  · intro i
    change 15 ≤ colorDegree c _ (coreEmbedding c r X Y hXm hYm (coreX i))
    rw [coreEmbedding_X]
    exact hG.first_opposite_high _ (hXm i)
  · intro i
    change 15 ≤ colorDegree c _ (coreEmbedding c r X Y hXm hYm (coreY i))
    rw [coreEmbedding_Y]
    exact hG.second_opposite_high _ (hYm i)

#print axioms remaining_core_realized
end PricingG
