import UniformK60.BalancedHostBraceCoordinates
import UniformK60.BalancedHostBraceRealSupport
import UniformK60.BalancedHostBraceMarked

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.BalancedHostBraceRealization
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers UniformK60.HostNormalization
open UniformK60.ClassificationAdapter
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedHost UniformK60.BalancedHostBraceFrame
open UniformK60.BalancedHostBraceGeometry UniformK60.BalancedHostBraceRow
open UniformK60.BalancedHostBracePlacement UniformK60.BalancedHostBraceMembership
open UniformK60.BalancedHostBraceFacts UniformK60.BalancedHostBraceCoordinates
open UniformK60.BalancedHostBraceMarked UniformK60.BalancedHostBraceRealSupport
open UniformK60.BalancedEncodingBraces CompletionC.NativeMatrices

private theorem native_palette (own : Color) (q : Fin 3) :
    (foreignEquiv own q).val=palette (foreign own q) := by fin_cases own <;> fin_cases q <;> rfl

/-- A projected row and an actual marked15 orbit are placed simultaneously
in the original60-vertex host. Every raw positive and negative input fact is
then a theorem about that one physical coloring. -/
theorem realize {c : Host} {root mark : Vertex} {g : Geometry}
    (hc : NoMonochromaticTriangle c) (caps : BalancedRawRoot.RawCaps c)
    (hd : ∀ q : Color,colorDegree c (palette q) root=BalancedRawRoot.rawDegree q)
    (a : ActualFrame c root mark g)
    (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600)
    (hmat : ∀ u v : Fin (rowShape (target g i)).dimension,u≠v →
      c (rowEmbedding g a.frame p i u) (rowEmbedding g a.frame p i v)=
        palette (rowMatrix (target g i) (rowPadded g i u) (rowPadded g i v)))
    (m : MarkChoice)
    (n : PhysicalNeighborhoodMap c root (palette 3) (R4333.k15Template (markedKind m)))
    (np : n.colors=foreignEquiv 3) (nmark : n.vertex (markedPosition m)=mark) :
    ∃ d : Host,NoMonochromaticTriangle d ∧ BalancedRawRoot.RawCaps d ∧
      Core.UnitsMatch d (rawUnits (target g i) m) := by
  let r := target g i
  have hm : mark∈colorNeighborhood c (palette 3) root := by
    simpa only [a.root_eq,a.mark_eq] using a.frame.mark_mem
  have hf : ∀ j,rowFree a p i j∈colorNeighborhood c (palette 0) root := by
    intro j
    exact (mem_inter.mp (image_mem (rowFree a p i) (rowFree_image a p i) j)).2
  have hfake : ∀ j,rowFake a p i j∈colorNeighborhood c (palette 1) root := by
    intro j
    exact (mem_inter.mp (image_mem (rowFake a p i) (rowFake_image a p i) j)).2
  obtain ⟨e,he0,he,hef,hefake,hereal,hemarked⟩ := place (rowFreeSizeLe r) root
    (rowFree a p i) (rowFake a p i) (rowReal a i).vertex (markedMap n) hd hf hfake
      (rowReal a i).mem_neighborhood (fun j => n.mem_neighborhood _)
  have hem : e 59=mark := (hemarked 14).trans (markedMap_last n nmark)
  let d := relabel c e (Equiv.refl _)
  have good : NoMonochromaticTriangle d := relabel_noMono c hc _ _
  have capsd : BalancedRawRoot.RawCaps d := by
    intro v q
    rw [relabel_degree]
    exact caps (e v) q
  refine ⟨d,good,capsd,raw_units_match ?_⟩
  refine { spokes := ?_,real := ?_,marked := ?_,matrix := ?_,membership := ?_ }
  · intro v hv
    exact relabel_root_spoke c root (Equiv.refl _) cell e he0 he v _ (by simp [cell,hv])
  · intro u v huv
    change c (e (realVertex u)) (e (realVertex v))=_
    rw [hereal,hereal,(rowReal a i).map_color _ _ huv,rowReal_palette,native_palette]
  · intro u v huv
    change c (e (markedVertex u)) (e (markedVertex v))=_
    rw [hemarked,hemarked]
    change c (n.vertex (markedOrder m u)) (n.vertex (markedOrder m v))=_
    rw [n.map_color _ _ ((markedOrder_bijective m).1.ne huv),np,native_palette,
      ClassificationFixedPalette.k15Template_castSucc]
  · intro u v huv hu hv
    change c (e (rawSupport r u)) (e (rawSupport r v))=_
    rw [placed_support a p i e hef hefake hereal u hu,placed_support a p i e hef hefake hereal v hv]
    have hn : (⟨u.val,hu⟩ : Fin (rowShape r).dimension)≠⟨v.val,hv⟩ := by
      intro h;apply huv;exact Fin.ext (congrArg (fun x : Fin (rowShape r).dimension => x.val) h)
    exact hmat _ _ hn
  · intro v hpos hlt
    have hfree : ∀ v,e v∈support c root mark 0 ↔ v∈freeSet r := by
      intro v
      rw [←rowFree_image a p i]
      exact image_pullback e (freeVertex (rowFreeSizeLe r)) (rowFree a p i) hef v
    have hfake' : ∀ v,e v∈support c root mark 1 ↔ v∈fakeSet := by
      intro v
      rw [←rowFake_image a p i]
      exact image_pullback e fakeVertex (rowFake a p i) hefake v
    have hreal : ∀ v,e v∈support c root mark 2 ↔ v∈realSet r := by
      intro v
      rw [←real_image a p i]
      exact image_pullback e
        (fun j : Fin (rowShape r).right => realVertex (BalancedProjectedRowSupport.realOrder r j))
        (fun j : Fin (rowShape r).right => (rowReal a i).vertex (BalancedProjectedRowSupport.realOrder r j))
        (fun j => hereal _) v
    exact membership_after_placement hc root mark hm r e he0 hem hfree hfake' hreal v
      (by intro h;have hh:=congrArg Fin.val h;omega)

#print axioms realize
end UniformK60.BalancedHostBraceRealization
