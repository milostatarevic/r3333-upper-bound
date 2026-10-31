import UniformK60.BalancedEncodingBraceMaps
import UniformK60.BalancedRawRoot

/-! The literal raw brace coordinates and palette are changed once, on all
sixty actual vertices, to the exact mixed compatibility prefix. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace UniformK60.BalancedEncodingBraces
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.Core (PhysicalUnit UnitMatches UnitsMatch unitsCNF)
open UniformK60.BalancedProjectedData UniformK60.BalancedHost UniformK60.HostNormalization
open UniformK61.BalancedEncoding (mem_pairs)

abbrev RawCaps := BalancedRawRoot.RawCaps

def cycleColor (q : Fin 3) : Fin 3 := ⟨(q.val+1)%3,Nat.mod_lt _ (by decide)⟩
def cycleMinor (kind : Bool) (i : Fin 15) : Fin 15 :=
  ⟨(cycle kind i.castSucc).val%15,Nat.mod_lt _ (by decide)⟩

theorem cycleMinor_full : ∀ kind i,(cycleMinor kind i).castSucc=cycle kind i.castSucc := by decide

theorem cycleMinor_bijective : ∀ kind,Function.Bijective (cycleMinor kind) := by decide

noncomputable def cycleEquiv (kind : Bool) : Fin 16≃Fin 16 := Equiv.ofBijective (cycle kind) (cycle_bijective kind)
noncomputable def minorEquiv (kind : Bool) : Fin 15≃Fin 15 := Equiv.ofBijective (cycleMinor kind) (cycleMinor_bijective kind)
noncomputable def markedEquiv (m : MarkChoice) : Fin 15≃Fin 15 := Equiv.ofBijective (markedOrder m) (markedOrder_bijective m)

theorem template_symm : ∀ kind a b,R4333.k16Template kind a b=R4333.k16Template kind b a := by decide

theorem root_map : ∀ kind m,mapVertex kind m 0=0 := by decide

theorem real_map : ∀ kind m (i : Fin 16),mapVertex kind m (vertex (29+i.val))=
    BalancedHost.yVertex false (cycle kind i) := by decide

theorem marked_map : ∀ kind m (i : Fin 15),mapVertex kind m (vertex (45+i.val))=
    BalancedHost.xVertex false (cycleMinor (markedKind m) (markedOrder m i)) := by decide

set_option maxRecDepth 100000 in
theorem root_color_map : ∀ kind m (v : Vertex),v≠0 →
    physicalColor (rawRootColor v)=BalancedEncodingData.rootColor (mapVertex kind m v) := by decide

theorem real_palette : ∀ q,physicalColor (foreign 2 q)=foreign 1 (cycleColor q) := by decide
theorem marked_palette : ∀ q,physicalColor (foreign 3 q)=foreign 0 (cycleColor q) := by decide

theorem raw_root_match {c : Coloring} {r : Row} {m : MarkChoice}
    (hu : UnitsMatch c (rawUnits r m)) (v : Vertex) (hv : v≠0) :
    c 0 v=palette (rawRootColor v) := by
  have h : positiveUnit 0 v (rawRootColor v)∈rawRootUnits :=
    List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨List.mem_finRange _,by simpa using hv⟩,rfl⟩
  have hfull : positiveUnit 0 v (rawRootColor v)∈rawUnits r m := by
    simp only [rawUnits,List.mem_append]
    tauto
  exact (hu _ hfull).2

theorem raw_real_match {c : Coloring} {r : Row} {m : MarkChoice}
    (hu : UnitsMatch c (rawUnits r m)) (a b : Fin 16) (hab : a≠b) :
    c (vertex (29+a.val)) (vertex (29+b.val))=palette (foreign 2 (R4333.k16Template (rowKind r) a b)) := by
  have ordered (a b : Fin 16) (h : a<b) :
      c (vertex (29+a.val)) (vertex (29+b.val))=palette (foreign 2 (R4333.k16Template (rowKind r) a b)) := by
    have hm : positiveUnit (vertex (29+a.val)) (vertex (29+b.val))
        (foreign 2 (R4333.k16Template (rowKind r) a b))∈rawRealUnits r :=
      List.mem_map.mpr ⟨(a,b),mem_pairs.mpr h,rfl⟩
    have hf : positiveUnit (vertex (29+a.val)) (vertex (29+b.val))
        (foreign 2 (R4333.k16Template (rowKind r) a b))∈rawUnits r m := by
      simp only [rawUnits,List.mem_append]
      tauto
    exact (hu _ hf).2
  rcases lt_or_gt_of_ne hab with h | h
  · exact ordered a b h
  · rw [c.color_symm,template_symm (rowKind r) a b]
    exact ordered b a h

theorem raw_marked_match {c : Coloring} {r : Row} {m : MarkChoice}
    (hu : UnitsMatch c (rawUnits r m)) (a b : Fin 15) (hab : a≠b) :
    c (vertex (45+a.val)) (vertex (45+b.val))=palette (foreign 3
      (R4333.k16Template (markedKind m) (markedOrder m a).castSucc (markedOrder m b).castSucc)) := by
  have ordered (a b : Fin 15) (h : a<b) :
      c (vertex (45+a.val)) (vertex (45+b.val))=palette (foreign 3
        (R4333.k16Template (markedKind m) (markedOrder m a).castSucc (markedOrder m b).castSucc)) := by
    have hm : positiveUnit (vertex (45+a.val)) (vertex (45+b.val))
        (foreign 3 (R4333.k16Template (markedKind m) (markedOrder m a).castSucc (markedOrder m b).castSucc))∈rawMarkedUnits m :=
      List.mem_map.mpr ⟨(a,b),mem_pairs.mpr h,rfl⟩
    have hf : positiveUnit (vertex (45+a.val)) (vertex (45+b.val))
        (foreign 3 (R4333.k16Template (markedKind m) (markedOrder m a).castSucc (markedOrder m b).castSucc))∈rawUnits r m := by
      simp only [rawUnits,List.mem_append]
      tauto
    exact (hu _ hf).2
  rcases lt_or_gt_of_ne hab with h | h
  · exact ordered a b h
  · rw [c.color_symm,template_symm (markedKind m) (markedOrder m a).castSucc (markedOrder m b).castSucc]
    exact ordered b a h

noncomputable def normalized (c : Coloring) (r : Row) (m : MarkChoice) : Coloring :=
  UnitTransport.transformed c (vertexEquiv r m).symm paletteEquiv

theorem normalized_map_color (c : Coloring) (r : Row) (m : MarkChoice)
    (a b : Vertex) (q : Color) (h : c a b=palette q) :
    normalized c r m (physicalVertex r m a) (physicalVertex r m b)=palette (physicalColor q) := by
  apply (UnitTransport.transformed_color c (vertexEquiv r m).symm paletteEquiv
    (physicalVertex r m a) (physicalVertex r m b) (physicalColor q)).mpr
  change c ((vertexEquiv r m).symm ((vertexEquiv r m) a))
    ((vertexEquiv r m).symm ((vertexEquiv r m) b))=
      palette (paletteEquiv.symm (paletteEquiv q))
  simpa only [Equiv.symm_apply_apply] using h

theorem normalized_eq_relabel (c : Coloring) (r : Row) (m : MarkChoice) :
    normalized c r m=relabel c (vertexEquiv r m).symm BalancedRawRoot.rotate.symm := by
  apply EdgeColoring.ext
  funext a b
  obtain ⟨q,hq⟩ := palette_surjective (c ((vertexEquiv r m).symm a) ((vertexEquiv r m).symm b))
  change UnitTransport.colorEquiv (paletteEquiv (UnitTransport.colorEquiv.symm
    (c ((vertexEquiv r m).symm a) ((vertexEquiv r m).symm b))))=
      BalancedRawRoot.rotate (c ((vertexEquiv r m).symm a) ((vertexEquiv r m).symm b))
  rw [←hq]
  change UnitTransport.colorEquiv (paletteEquiv (UnitTransport.colorEquiv.symm (UnitTransport.colorEquiv q)))=_
  rw [Equiv.symm_apply_apply]
  exact (BalancedRawRoot.rotate_palette q).symm

def inverseColor : Color → Color := ![3,2,0,1]
theorem inverse_palette : ∀ q,BalancedRawRoot.rotate.symm (palette q)=palette (inverseColor q) := by decide

theorem normalized_caps {c : Coloring} (r : Row) (m : MarkChoice) (hcaps : RawCaps c) :
    NamedCaps (normalized c r m) := by
  intro v q
  rw [normalized_eq_relabel,relabel_degree,inverse_palette]
  have h := hcaps ((vertexEquiv r m).symm v) (inverseColor q)
  fin_cases q <;> simpa [inverseColor] using h

theorem canonical_rootColor_map : ∀ v : Vertex,v≠0 →
    canonicalCell false v=some (palette (BalancedEncodingData.rootColor v)) := by decide

theorem normalized_spokes {c : Coloring} {r : Row} {m : MarkChoice}
    (hu : UnitsMatch c (rawUnits r m)) : Spokes false (normalized c r m) := by
  intro v
  obtain ⟨u,rfl⟩ := (physicalVertex_bijective r m).2 v
  by_cases hu0 : u=0
  · subst u
    simp [physicalVertex,mapVertex,vertex,Spokes,rootCell,canonicalCell]
  · have he := normalized_map_color c r m 0 u (rawRootColor u) (raw_root_match hu u hu0)
    have hroot : physicalVertex r m 0=0 := root_map (rowKind r) m
    rw [hroot] at he
    have hv : physicalVertex r m u≠0 := by
      intro h
      exact hu0 ((physicalVertex_bijective r m).1 (h.trans hroot.symm))
    have hq := root_color_map (rowKind r) m u hu0
    change physicalColor (rawRootColor u)=BalancedEncodingData.rootColor (physicalVertex r m u) at hq
    rw [hq] at he
    rw [canonical_rootColor_map _ hv]
    apply (rootCell_some _ 0 _ (Equiv.refl _) _).mpr
    exact (mem_colorNeighborhood _ _ _ _).mpr ⟨hv,he⟩

theorem normalized_real_template {c : Coloring} {r : Row} {m : MarkChoice}
    (hu : UnitsMatch c (rawUnits r m)) :
    TemplateAt (by decide) (normalized c r m) (BalancedHost.yVertex false) 1 (rowKind r) := by
  intro i j hij
  let a := (cycleEquiv (rowKind r)).symm i
  let b := (cycleEquiv (rowKind r)).symm j
  have hab : a≠b := (cycleEquiv (rowKind r)).symm.injective.ne hij
  have he := normalized_map_color c r m _ _ _ (raw_real_match hu a b hab)
  change normalized c r m (mapVertex (rowKind r) m _) (mapVertex (rowKind r) m _)=_ at he
  rw [real_map,real_map,real_palette] at he
  have hc := cycle_colors (rowKind r) a b hab
  change R4333.k16Template (rowKind r) (cycle (rowKind r) a) (cycle (rowKind r) b)=
    cycleColor (R4333.k16Template (rowKind r) a b) at hc
  rw [←hc] at he
  have ha : cycle (rowKind r) a=i := (cycleEquiv (rowKind r)).apply_symm_apply i
  have hb : cycle (rowKind r) b=j := (cycleEquiv (rowKind r)).apply_symm_apply j
  simpa only [ha,hb,Fin.castLE,Fin.castSucc,Fin.castAdd] using he

theorem normalized_marked_template {c : Coloring} {r : Row} {m : MarkChoice}
    (hu : UnitsMatch c (rawUnits r m)) :
    TemplateAt (firstSize_le false) (normalized c r m) (BalancedHost.xVertex false) 0 (markedKind m) := by
  intro i j hij
  let e := (markedEquiv m).trans (minorEquiv (markedKind m))
  let a := e.symm i
  let b := e.symm j
  have hab : a≠b := e.symm.injective.ne hij
  have he := normalized_map_color c r m _ _ _ (raw_marked_match hu a b hab)
  change normalized c r m (mapVertex (rowKind r) m _) (mapVertex (rowKind r) m _)=_ at he
  rw [marked_map,marked_map,marked_palette] at he
  have hneq : (markedOrder m a).castSucc≠(markedOrder m b).castSucc := by
    intro h
    apply hab
    apply (markedOrder_bijective m).1
    exact Fin.ext (congrArg (fun z : Fin 16 => z.val) h)
  have hc := cycle_colors (markedKind m) (markedOrder m a).castSucc (markedOrder m b).castSucc hneq
  rw [←cycleMinor_full,←cycleMinor_full] at hc
  change R4333.k16Template (markedKind m)
      (cycleMinor (markedKind m) (markedOrder m a)).castSucc
      (cycleMinor (markedKind m) (markedOrder m b)).castSucc=
    cycleColor (R4333.k16Template (markedKind m) (markedOrder m a).castSucc (markedOrder m b).castSucc) at hc
  rw [←hc] at he
  have ha : cycleMinor (markedKind m) (markedOrder m a)=i := e.apply_symm_apply i
  have hb : cycleMinor (markedKind m) (markedOrder m b)=j := e.apply_symm_apply j
  simpa only [ha,hb,Fin.castLE,Fin.castSucc,Fin.castAdd] using he

theorem normalized_from_raw_units (c : Coloring) (r : Row) (m : MarkChoice)
    (hcaps : RawCaps c) (hu : UnitsMatch c (rawUnits r m)) :
    Normalized false (normalized c r m) (owner (r,m)) :=
  ⟨normalized_caps r m hcaps,normalized_spokes hu,normalized_marked_template hu,normalized_real_template hu⟩

#print axioms normalized_from_raw_units
end UniformK60.BalancedEncodingBraces
