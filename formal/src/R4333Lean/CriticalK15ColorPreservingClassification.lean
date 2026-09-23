import R4333Lean.CriticalCatalogues
import R4333Lean.CriticalTemplatePaletteSymmetry
import R4333Lean.SingleRootStarWitness61
import R4333Lean.SingleRootStarWitness61

/-!
# Colour-preserving normalization of a critical K15

The checked K15 catalogue is stated up to simultaneous vertex and palette
relabeling.  For exchanging blocks in the threshold profiles, a palette
relabeling is inconvenient: the three host colours have already been fixed
by the distinguished root.  The full palette symmetry of each critical
template absorbs that relabeling into a second vertex permutation.

Consequently every triangle-free three-colouring of `K15` is, after changing
vertices only, exactly one of the two fixed `k15Template` colour tables.
-/

namespace R4333

/-- Every good three-colouring of `K15` has a colour-preserving vertex
normalization to one of the two checked critical templates. -/
theorem exists_colorPreserving_k15Template
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ twisted : Bool, ∃ vertex : Fin 15 ≃ Fin 15,
      ∀ u v, u ≠ v →
        c (vertex u) (vertex v) = k15Template twisted u v := by
  obtain ⟨template, htemplate, ⟨equiv⟩⟩ :=
    k15CriticalCatalogue_complete.2 c hc
  simp [k15CriticalCatalogue] at htemplate
  rcases htemplate with rfl | rfl
  · obtain ⟨paletteVertex, hpalette⟩ :=
      k15Template_fullPaletteSymmetry false equiv.colors
    refine ⟨false, paletteVertex.trans equiv.vertex.symm, ?_⟩
    intro u v huv
    apply equiv.colors.injective
    calc
      equiv.colors
          (c ((paletteVertex.trans equiv.vertex.symm) u)
            ((paletteVertex.trans equiv.vertex.symm) v)) =
          k15Untwisted (paletteVertex u) (paletteVertex v) := by
            simpa using equiv.map_color
              (equiv.vertex.symm (paletteVertex u))
              (equiv.vertex.symm (paletteVertex v))
              (equiv.vertex.symm.injective.ne
                (paletteVertex.injective.ne huv))
      _ = equiv.colors (k15Untwisted u v) := hpalette u v huv
      _ = equiv.colors (k15Template false u v) := by
        simp [k15Template]
  · obtain ⟨paletteVertex, hpalette⟩ :=
      k15Template_fullPaletteSymmetry true equiv.colors
    refine ⟨true, paletteVertex.trans equiv.vertex.symm, ?_⟩
    intro u v huv
    apply equiv.colors.injective
    calc
      equiv.colors
          (c ((paletteVertex.trans equiv.vertex.symm) u)
            ((paletteVertex.trans equiv.vertex.symm) v)) =
          k15Twisted (paletteVertex u) (paletteVertex v) := by
            simpa using equiv.map_color
              (equiv.vertex.symm (paletteVertex u))
              (equiv.vertex.symm (paletteVertex v))
              (equiv.vertex.symm.injective.ne
                (paletteVertex.injective.ne huv))
      _ = equiv.colors (k15Twisted u v) := hpalette u v huv
      _ = equiv.colors (k15Template true u v) := by
        simp [k15Template]

/-! ## A fixed four-colour host palette -/

/-- The canonical three-colour palette as an equivalence onto the host
colours other than `block`. -/
noncomputable def nonBlockPaletteEquiv (block : Fin 4) :
    Fin 3 ≃ {q : Fin 4 // q ≠ block} :=
  Equiv.ofBijective
    (fun q : Fin 3 => ⟨SingleRootStarCNF.canonicalPalette block q,
      SingleRootStarWitness61.canonicalPalette_ne_block block q⟩)
    (by
      rw [Fintype.bijective_iff_injective_and_card]
      constructor
      · intro left right h
        apply SingleRootStarWitness61.canonicalPalette_injective block
        exact congrArg Subtype.val h
      · simp)

/-- Decode a host colour through the canonical non-block palette.  The
fallback branch is used only on the irrelevant diagonal in applications. -/
noncomputable def decodeNonBlockColor (block q : Fin 4) : Fin 3 :=
  if h : q ≠ block then (nonBlockPaletteEquiv block).symm ⟨q, h⟩ else 0

theorem canonicalPalette_decodeNonBlockColor
    (block q : Fin 4) (hq : q ≠ block) :
    SingleRootStarCNF.canonicalPalette block
        (decodeNonBlockColor block q) = q := by
  simp only [decodeNonBlockColor, dif_pos hq]
  change ((nonBlockPaletteEquiv block
    ((nonBlockPaletteEquiv block).symm ⟨q, hq⟩)).val) = q
  rw [Equiv.apply_symm_apply]

/-- Forget a fixed omitted host colour, decoding the other three colours
through the canonical palette. -/
noncomputable def decodeNonBlockColoring (block : Fin 4)
    (c : EdgeColoring (Fin 15) (Fin 4)) :
    EdgeColoring (Fin 15) ThreeColor where
  color u v := decodeNonBlockColor block (c u v)
  color_symm u v := congrArg (decodeNonBlockColor block) (c.color_symm u v)

theorem decodeNonBlockColoring_noMono
    (block : Fin 4) (c : EdgeColoring (Fin 15) (Fin 4))
    (hc : NoMonochromaticTriangle c)
    (havoids : ∀ u v, u ≠ v → c u v ≠ block) :
    NoMonochromaticTriangle (decodeNonBlockColoring block c) := by
  intro u v w hdistinct hmono
  apply hc u v w hdistinct
  have huv := canonicalPalette_decodeNonBlockColor block (c u v)
    (havoids u v hdistinct.1)
  have huw := canonicalPalette_decodeNonBlockColor block (c u w)
    (havoids u w hdistinct.2.1)
  have hvw := canonicalPalette_decodeNonBlockColor block (c v w)
    (havoids v w hdistinct.2.2)
  constructor
  · exact huv.symm.trans ((congrArg
      (SingleRootStarCNF.canonicalPalette block) hmono.1).trans huw)
  · exact huw.symm.trans ((congrArg
      (SingleRootStarCNF.canonicalPalette block) hmono.2).trans hvw)

/-- Host-palette form used by block exchange: a triangle-free `K15` whose
edges all avoid one host colour is, by vertices alone, one of the two exact
canonical K15 blocks in the complementary palette. -/
theorem exists_colorPreserving_hostK15Template
    (block : Fin 4) (c : EdgeColoring (Fin 15) (Fin 4))
    (hc : NoMonochromaticTriangle c)
    (havoids : ∀ u v, u ≠ v → c u v ≠ block) :
    ∃ twisted : Bool, ∃ vertex : Fin 15 ≃ Fin 15,
      ∀ u v, u ≠ v →
        c (vertex u) (vertex v) =
          SingleRootStarCNF.canonicalPalette block
            (k15Template twisted u v) := by
  obtain ⟨twisted, vertex, hvertex⟩ :=
    exists_colorPreserving_k15Template
      (decodeNonBlockColoring block c)
      (decodeNonBlockColoring_noMono block c hc havoids)
  refine ⟨twisted, vertex, ?_⟩
  intro u v huv
  have hne : vertex u ≠ vertex v := vertex.injective.ne huv
  calc
    c (vertex u) (vertex v) =
        SingleRootStarCNF.canonicalPalette block
          (decodeNonBlockColoring block c (vertex u) (vertex v)) :=
      (canonicalPalette_decodeNonBlockColor block
        (c (vertex u) (vertex v)) (havoids _ _ hne)).symm
    _ = SingleRootStarCNF.canonicalPalette block
          (k15Template twisted u v) := congrArg
      (SingleRootStarCNF.canonicalPalette block) (hvertex u v huv)

#print axioms R4333.exists_colorPreserving_k15Template
#print axioms R4333.exists_colorPreserving_hostK15Template

end R4333
