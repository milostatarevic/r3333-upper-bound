import CompletionC.CommonBlocks
import PricingIntegration.DFrameDegrees
import PricingG.DSelectedRowSplit
import PricingG.DKindReduction

set_option autoImplicit false
set_option maxHeartbeats 0
namespace PricingG.UUQPhysicalExtension
open Ramsey61 Finset
open Ramsey61.CEncodingCore (palette palette_injective)
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.DFrameColoring PricingIntegration.DFrameDegrees
open CompletionC.CommonBlocks
open R4333.ProfileDTripleJoinReduction
variable {c : Host} {five : Bool} {t : Types}

noncomputable def lowEquiv (b : Blocks c (layout five) t) :
    Fin 14 ≃ colorNeighborhood c (palette 0) b.root := by
  classical
  have hd : (colorNeighborhood c (palette 0) b.root).card = 14 := by
    have h:=b.low_degree
    change colorDegree c (palette 0) b.root = 14
    simpa [layout,lowSize,tailSize,leftSize,leftLarge,rightSize,rightLarge] using h
  exact (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hd)).symm

noncomputable def low (b : Blocks c (layout five) t) : Fin 14 ↪ Fin 61 :=
  (lowEquiv b).toEmbedding.trans (Function.Embedding.subtype _)

theorem low_mem (b : Blocks c (layout five) t) (i : Fin 14) :
    low b i ∈ colorNeighborhood c (palette 0) b.root := (lowEquiv b i).property

noncomputable def full (b : Blocks c (layout five) t) : Fin 14 ⊕ Fin 46 → Fin 61
  | .inl i => low b i
  | .inr i => tailEmbedding (frame b) i

theorem tail_ne_root (b : Blocks c (layout five) t) (i : Fin 46) :
    tailEmbedding (frame b) i ≠ b.root := (frame b).ne_root _

theorem tail_not_low (b : Blocks c (layout five) t) (i : Fin 46) :
    tailEmbedding (frame b) i ∉ colorNeighborhood c (palette 0) b.root := by
  intro h
  have hs := (frame b).spokes (tailIndex five i)
  have he := (mem_colorNeighborhood _ _ _ _).mp h |>.2
  have ho := palette_injective (hs.symm.trans he)
  exact (ABLayout.owner_tail_nonzero (layout five) i) ho

theorem full_injective (b : Blocks c (layout five) t) : Function.Injective (full b) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl ((low b).injective h)
    | inr y =>
      change low b x = tailEmbedding (frame b) y at h
      exact False.elim (tail_not_low b y (h ▸ low_mem b x))
  | inr x =>
    cases y with
    | inl y =>
      change tailEmbedding (frame b) x = low b y at h
      exact False.elim (tail_not_low b x (h.symm ▸ low_mem b y))
    | inr y => exact congrArg Sum.inr ((tailEmbedding (frame b)).injective h)

theorem full_ne_root (b : Blocks c (layout five) t) (x : Fin 14 ⊕ Fin 46) :
    full b x ≠ b.root := by
  cases x with
  | inl x => exact ((mem_colorNeighborhood _ _ _ _).mp (low_mem b x)).1
  | inr x => exact tail_ne_root b x

theorem full_image (b : Blocks c (layout five) t) :
    Finset.univ.image (full b) = Finset.univ.erase b.root := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
    simp [full_ne_root b x]
  · rw [Finset.card_image_of_injective _ (full_injective b)]
    simp

noncomputable def fullColoring (b : Blocks c (layout five) t) :
    R4333.EdgeColoring (Fin 14 ⊕ Fin 46) (Fin 4) where
  color u v := paletteEquiv.symm (c (full b u) (full b v))
  color_symm u v := congrArg paletteEquiv.symm (c.color_symm _ _)

theorem full_good (b : Blocks c (layout five) t) (hc : NoMonochromaticTriangle c) :
    R4333.NoMonochromaticTriangle (fullColoring b) := by
  intro u v w hd hm
  exact hc (full b u) (full b v) (full b w)
    ⟨(full_injective b).ne hd.1,(full_injective b).ne hd.2.1,(full_injective b).ne hd.2.2⟩
    ⟨paletteEquiv.symm.injective hm.1,paletteEquiv.symm.injective hm.2⟩

theorem coloring_left (b : Blocks c (layout five) t) (u v : Fin 15) (hne : u≠v) :
    coloring (frame b) (ABLayout.left (layout five) u) (ABLayout.left (layout five) v)=
      R4333.SingleRootStarCNF.canonicalPalette 1 (R4333.k15Template t.left u v) := by
  apply (Equiv.symm_apply_eq paletteEquiv).mpr
  change c ((frame b).vertex (ABLayout.left (layout five) u)) ((frame b).vertex (ABLayout.left (layout five) v)) = palette _
  have h : c ((frame b).vertex (ABLayout.left (layout five) u)) ((frame b).vertex (ABLayout.left (layout five) v)) = palette (foreign 1 (R4333.k15Template t.left u v)) := left_edges b u v hne
  simpa only [foreign_eq_canonical] using h

theorem coloring_right (b : Blocks c (layout five) t) (u v : Fin 15) (hne : u≠v) :
    coloring (frame b) (ABLayout.right (layout five) u) (ABLayout.right (layout five) v)=
      R4333.SingleRootStarCNF.canonicalPalette 2 (R4333.k15Template t.right u v) := by
  apply (Equiv.symm_apply_eq paletteEquiv).mpr
  change c ((frame b).vertex (ABLayout.right (layout five) u)) ((frame b).vertex (ABLayout.right (layout five) v)) = palette _
  have h : c ((frame b).vertex (ABLayout.right (layout five) u)) ((frame b).vertex (ABLayout.right (layout five) v)) = palette (foreign 2 (R4333.k15Template t.right u v)) := right_edges b u v hne
  simpa only [foreign_eq_canonical] using h

theorem coloring_marked (b : Blocks c (layout five) t) (u v : Fin 16) (hne : u≠v) :
    coloring (frame b) (ABLayout.marked (layout five) u) (ABLayout.marked (layout five) v)=
      R4333.SingleRootStarCNF.canonicalPalette 3 (R4333.k16Template t.marked u v) := by
  apply (Equiv.symm_apply_eq paletteEquiv).mpr
  change c ((frame b).vertex (ABLayout.marked (layout five) u)) ((frame b).vertex (ABLayout.marked (layout five) v)) = palette _
  simpa only [foreign_eq_canonical] using marked_edges b u v hne

theorem tail_templates {c : Host} {five : Bool} (bl : Blocks c (layout five) t) (block : Fin 3) (a b : Nat)
    (ha : a<blockSize block) (hb : b<blockSize block) (hab : a<b) :
    tailColoring (frame bl) (blockVertex block a) (blockVertex block b)=
      R4333.SingleRootStarCNF.canonicalPalette (Fin.succ block)
        (R4333.SingleRootStarCNF.templateColor (blockSize block) ((kind t).twisted block) a b) := by
  fin_cases block
  · let u : Fin 15:=⟨a,ha⟩
    let v : Fin 15:=⟨b,hb⟩
    have h:=coloring_left bl u v (Fin.ne_of_lt hab)
    change coloring (frame bl) (tailIndex five (blockVertex 0 u.val)) (tailIndex five (blockVertex 0 v.val)) = _
    rw [tailIndex_left,tailIndex_left]
    simp only [kind,Kind.twisted_ofBooleans]
    change coloring (frame bl) (ABLayout.left (layout five) u) (ABLayout.left (layout five) v) =
      R4333.SingleRootStarCNF.canonicalPalette 1 (R4333.k15Template t.left ⟨a%15,by omega⟩ ⟨b%15,by omega⟩)
    simpa only [Nat.mod_eq_of_lt (show a<15 from ha),Nat.mod_eq_of_lt (show b<15 from hb)] using h
  · let u : Fin 15:=⟨a,ha⟩
    let v : Fin 15:=⟨b,hb⟩
    have h:=coloring_right bl u v (Fin.ne_of_lt hab)
    change coloring (frame bl) (tailIndex five (blockVertex 1 u.val)) (tailIndex five (blockVertex 1 v.val)) = _
    rw [tailIndex_right,tailIndex_right]
    simp only [kind,Kind.twisted_ofBooleans]
    change coloring (frame bl) (ABLayout.right (layout five) u) (ABLayout.right (layout five) v) =
      R4333.SingleRootStarCNF.canonicalPalette 2 (R4333.k15Template t.right ⟨a%15,by omega⟩ ⟨b%15,by omega⟩)
    simpa only [Nat.mod_eq_of_lt (show a<15 from ha),Nat.mod_eq_of_lt (show b<15 from hb)] using h
  · let u : Fin 16:=⟨a,ha⟩
    let v : Fin 16:=⟨b,hb⟩
    have h:=coloring_marked bl u v (Fin.ne_of_lt hab)
    change coloring (frame bl) (tailIndex five (blockVertex 2 u.val)) (tailIndex five (blockVertex 2 v.val)) = _
    rw [tailIndex_marked,tailIndex_marked]
    simp only [kind,Kind.twisted_ofBooleans]
    change coloring (frame bl) (ABLayout.marked (layout five) u) (ABLayout.marked (layout five) v) =
      R4333.SingleRootStarCNF.canonicalPalette 3 (R4333.k16Template t.marked ⟨a%16,by omega⟩ ⟨b%16,by omega⟩)
    simpa only [Nat.mod_eq_of_lt (show a<16 from ha),Nat.mod_eq_of_lt (show b<16 from hb)] using h


noncomputable def witness (b : Blocks c (layout five) t) (hc : NoMonochromaticTriangle c) :
    Witness (kind t) where
  coloring := tailColoring (frame b)
  noMono := R4333.noMono_pullback (coloring (frame b)) (tailIndex five)
    (tailIndex_injective five) (coloring_good (frame b) hc)
  templateCanonical := tail_templates b

noncomputable def inside (b : Blocks c (layout five) t) : R4333.EdgeColoring (Fin 14) (Fin 4) :=
  R4333.pullbackColoring (fullColoring b) Sum.inl

noncomputable def rows (b : Blocks c (layout five) t) (a : Fin 14) (x : Fin 46) : Fin 4 :=
  fullColoring b (.inl a) (.inr x)

theorem joined_eq (b : Blocks c (layout five) t) :
    R4333.ColoringJoinRows.joinColoring (inside b) (tailColoring (frame b)) (rows b) = fullColoring b := by
  ext u v
  cases u <;> cases v <;>
    simp [R4333.ColoringJoinRows.joinColoring,inside,rows,fullColoring,full,
      PricingIntegration.DFrameColoring.tailColoring,coloring,PricingIntegration.DFrameDegrees.tailEmbedding,R4333.pullbackColoring,c.color_symm]

theorem inside_forbidden (b : Blocks c (layout five) t) (hc : NoMonochromaticTriangle c)
    (u v : Fin 14) (hne : u≠v) : inside b u v≠0 := by
  intro h
  have he : c (low b u) (low b v)=palette 0 := (Equiv.symm_apply_eq paletteEquiv).mp h
  exact neighborhood_avoids_own_color c hc (low_mem b u) (low_mem b v) ((low b).injective.ne hne) he

noncomputable def extension (b : Blocks c (layout five) t) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDRowExtension.Extension (kind t) := by
  have hj : R4333.NoMonochromaticTriangle
      (R4333.ColoringJoinRows.joinColoring (inside b) (tailColoring (frame b)) (rows b)) := by
    rw [joined_eq];exact full_good b hc
  have hd := (R4333.ColoringJoinRows.noMono_joinColoring_iff _ _ _).mp hj
  exact {
    tail := witness b hc
    inside := inside b
    rows := rows b
    insideNoMono := hd.1
    insideRootForbidden := inside_forbidden b hc
    rowsAdmissible := hd.2.2.1
    rowsPairCompatible := hd.2.2.2 }

theorem full_joined_eq (b : Blocks c (layout five) t) (hc : NoMonochromaticTriangle c) :
    R4333.ProfileDRowSupportBounds61.fullJoinedColoring (extension b hc)=fullColoring b := joined_eq b

theorem neighbor_image (b : Blocks c (layout five) t) (u : Fin 14 ⊕ Fin 46) (q : Fin 4) :
    (R4333.colorNeighborhood (fullColoring b) q u).image (full b) =
      (colorNeighborhood c (palette q) (full b u)).erase b.root := by
  classical
  ext y
  simp only [Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨hne,hcol⟩ := (R4333.mem_colorNeighborhood _ _ _ _).mp hx
    refine ⟨full_ne_root b x,(mem_colorNeighborhood _ _ _ _).mpr ⟨(full_injective b).ne hne,?_⟩⟩
    exact (Equiv.symm_apply_eq paletteEquiv).mp hcol
  · rintro ⟨hyr,hy⟩
    have him : y∈Finset.univ.image (full b) := by rw [full_image];simp [hyr]
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp him
    obtain ⟨hne,hcol⟩ := (mem_colorNeighborhood _ _ _ _).mp hy
    refine ⟨x,(R4333.mem_colorNeighborhood _ _ _ _).mpr ⟨fun he=>hne (congrArg (full b) he),?_⟩,rfl⟩
    exact (Equiv.symm_apply_eq paletteEquiv).mpr hcol

theorem full_mark (b : Blocks c (layout five) t) :
    full b (.inr (45 : Fin 46))=b.marked.vertex 15 := by
  change (frame b).vertex (tailIndex five (blockVertex 2 15))=_
  exact (congrArg (frame b).vertex (tailIndex_marked five (15 : Fin 16))).trans (physical_marked b 15)

theorem selected_high (b : Blocks c (layout five) t) (hc : NoMonochromaticTriangle c) :
    14≤R4333.colorDegree (R4333.ProfileDRowSupportBounds61.fullJoinedColoring (extension b hc))
      (3 : Fin 4) (.inr (45 : Fin 46)) := by
  classical
  rw [full_joined_eq]
  have hh:=b.marked_high
  have hroot : b.root∈colorNeighborhood c (palette 3) (b.marked.vertex 15) := by
    obtain ⟨hne,he⟩ := (mem_colorNeighborhood _ _ _ _).mp (b.marked.mem_neighborhood 15)
    exact (mem_colorNeighborhood _ _ _ _).mpr ⟨hne.symm,by rw [c.color_symm];exact he⟩
  have hcimage := congrArg Finset.card (neighbor_image b (.inr (45 : Fin 46)) 3)
  rw [Finset.card_image_of_injective _ (full_injective b),full_mark] at hcimage
  have hcard:=Finset.card_erase_add_one hroot
  change 15≤(colorNeighborhood c (palette 3) (b.marked.vertex 15)).card at hh
  change 14≤(R4333.colorNeighborhood (fullColoring b) 3 (.inr (45 : Fin 46))).card
  omega

theorem selected_split (b : Blocks c (layout five) t) (hc : NoMonochromaticTriangle c) :
    (∃e : R4333.ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension (kind t), e.block=2) ∨
    (∃e : R4333.ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension (kind t), e.block=2) := by
  have hh:=selected_high b hc
  rcases DSelectedRowSplit.exists_selected_high_row_split (extension b hc) 2 (Fin.last 15) hh with
    ⟨_,e,he,_⟩|⟨_,e,he,_⟩
  · exact Or.inl ⟨e,he⟩
  · exact Or.inr ⟨e,he⟩

#print axioms selected_split

end PricingG.UUQPhysicalExtension
