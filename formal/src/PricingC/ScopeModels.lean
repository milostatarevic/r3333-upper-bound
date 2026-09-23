import Ramsey61.ClassificationAdapter
import R4333Lean.CriticalTemplatePaletteSymmetry
import R4333Lean.CriticalTemplateShadowLaws
import Ramsey61.CAnchorGeometry

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter

/-- A physical embedding exhausting one actual neighborhood, with a prescribed
single palette. This changes coordinates, not the host edge colors. -/
structure FixedPaletteMap (c : Host) (owner : Vertex) (omitted : FourColor)
    {n : Nat} (template : R4333.EdgeColoring (Fin n) (Fin 3))
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) where
  vertex : Fin n ↪ Vertex
  mem_scope : ∀ i, vertex i ∈ colorNeighborhood c omitted owner
  covers : ∀ v ∈ colorNeighborhood c omitted owner, ∃ i, vertex i = v
  map_color : ∀ i j, i ≠ j → c (vertex i) (vertex j) = (palette (template i j)).val

theorem fixed_palette_k16 (c : Host) (hc : NoMonochromaticTriangle c)
    (owner : Vertex) (omitted : FourColor) (hd : colorDegree c omitted owner = 16)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) :
    ∃ t : Bool, Nonempty (FixedPaletteMap c owner omitted (R4333.k16Template t) palette) := by
  classical
  obtain ⟨template, ht, ⟨m⟩⟩ := physical_neighborhood_k16 c hc owner omitted hd
  have htemplate : ∃ t : Bool, template = R4333.k16Template t := by
    simp only [R4333.k16CriticalCatalogue,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  obtain ⟨t,rfl⟩ := htemplate
  let perm := palette.trans m.colors.symm
  obtain ⟨e,he⟩ := R4333.k16Template_fullPaletteSymmetry t perm
  refine ⟨t, ⟨?_⟩⟩
  refine {
    vertex := e.toEmbedding.trans m.vertex
    mem_scope := fun i => m.mem_neighborhood (e i)
    covers := ?_
    map_color := ?_ }
  · intro v hv
    obtain ⟨i,hi⟩ := m.covers_neighborhood v hv
    exact ⟨e.symm i,by simpa using hi⟩
  · intro i j hij
    change c (m.vertex (e i)) (m.vertex (e j)) = _
    rw [m.map_color _ _ (e.injective.ne hij),he i j hij]
    simp [perm]

theorem fixed_palette_k15 (c : Host) (hc : NoMonochromaticTriangle c)
    (owner : Vertex) (omitted : FourColor) (hd : colorDegree c omitted owner = 15)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) :
    ∃ t : Bool, Nonempty (FixedPaletteMap c owner omitted (R4333.k15Template t) palette) := by
  classical
  obtain ⟨template, ht, ⟨m⟩⟩ := physical_neighborhood_k15 c hc owner omitted hd
  have htemplate : ∃ t : Bool, template = R4333.k15Template t := by
    simp only [R4333.k15CriticalCatalogue,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  obtain ⟨t,rfl⟩ := htemplate
  let perm := palette.trans m.colors.symm
  obtain ⟨e,he⟩ := R4333.k15Template_fullPaletteSymmetry t perm
  refine ⟨t, ⟨?_⟩⟩
  refine {
    vertex := e.toEmbedding.trans m.vertex
    mem_scope := fun i => m.mem_neighborhood (e i)
    covers := ?_
    map_color := ?_ }
  · intro v hv
    obtain ⟨i,hi⟩ := m.covers_neighborhood v hv
    exact ⟨e.symm i,by simpa using hi⟩
  · intro i j hij
    change c (m.vertex (e i)) (m.vertex (e j)) = _
    rw [m.map_color _ _ (e.injective.ne hij),he i j hij]
    simp [perm]

/-- A completion contains at most one formal position. Every present position
is mapped injectively onto the exact physical scope; absent positions are
not interpreted as additional host vertices. -/
structure CompletedScope (c : Host) (owner : Vertex) (omitted : FourColor)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) where
  model : R4333.EdgeColoring (Fin 16) (Fin 3)
  good : R4333.NoMonochromaticTriangle model
  present : Finset (Fin 16)
  large : 15 ≤ present.card
  vertex : present ↪ Vertex
  mem_scope : ∀ i, vertex i ∈ colorNeighborhood c omitted owner
  covers : ∀ v ∈ colorNeighborhood c omitted owner, ∃ i, vertex i = v
  map_color : ∀ i j : present, i ≠ j →
    c (vertex i) (vertex j) = (palette (model i.val j.val)).val

def visible15 : Finset (Fin 16) := Finset.univ.erase 15

def visible15Index (i : visible15) : Fin 15 :=
  ⟨i.val.val,by
    have hi := (Finset.mem_erase.mp i.property).1
    have hb := i.val.isLt
    have hn : i.val.val ≠ 15 := fun h => hi (Fin.ext h)
    omega⟩

theorem visible15Index_injective : Function.Injective visible15Index := by
  intro i j h
  apply Subtype.ext
  apply Fin.ext
  exact congrArg (fun x : Fin 15 => x.val) h

def visible15OfIndex (i : Fin 15) : visible15 := by
  refine ⟨⟨i.val, Nat.lt_trans i.isLt (by decide)⟩, ?_⟩
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  intro heq
  have hval := congrArg (fun x : Fin 16 => x.val) heq
  have hi := i.isLt
  change i.val = 15 at hval
  omega

theorem k15_as_restriction (t : Bool) (i j : visible15) :
    R4333.k15Template t (visible15Index i) (visible15Index j) =
      R4333.k16Template t i.val j.val := by
  cases t <;> rfl

def completed_from_k16 (c : Host) (owner : Vertex) (omitted : FourColor)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) (t : Bool)
    (m : FixedPaletteMap c owner omitted (R4333.k16Template t) palette) :
    CompletedScope c owner omitted palette where
  model := R4333.k16Template t
  good := by cases t <;> simp [R4333.k16Template,R4333.k16Untwisted_good,R4333.k16Twisted_good]
  present := Finset.univ
  large := by simp
  vertex := ⟨fun i => m.vertex i.val,fun i j h => Subtype.ext (m.vertex.injective h)⟩
  mem_scope := fun i => m.mem_scope i.val
  covers := by intro v hv; obtain ⟨i,hi⟩ := m.covers v hv; exact ⟨⟨i,by simp⟩,hi⟩
  map_color := by intro i j hij; exact m.map_color i.val j.val (fun h => hij (Subtype.ext h))

def completed_from_k15 (c : Host) (owner : Vertex) (omitted : FourColor)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) (t : Bool)
    (m : FixedPaletteMap c owner omitted (R4333.k15Template t) palette) :
    CompletedScope c owner omitted palette where
  model := R4333.k16Template t
  good := by cases t <;> simp [R4333.k16Template,R4333.k16Untwisted_good,R4333.k16Twisted_good]
  present := visible15
  large := by simp [visible15]
  vertex := ⟨fun i => m.vertex (visible15Index i),fun i j h => visible15Index_injective (m.vertex.injective h)⟩
  mem_scope := fun i => m.mem_scope (visible15Index i)
  covers := by
    intro v hv
    obtain ⟨i,hi⟩ := m.covers v hv
    exact ⟨visible15OfIndex i,hi⟩
  map_color := by
    intro i j hij
    rw [←k15_as_restriction]
    exact m.map_color _ _ (visible15Index_injective.ne hij)

/-- A genuine high neighborhood admits a physical partial K16 model with
one prescribed palette and at most one absent reference position. -/
theorem high_neighborhood_completion (c : Host) (hc : NoMonochromaticTriangle c)
    (owner : Vertex) (omitted : FourColor) (hhigh : 15 ≤ colorDegree c omitted owner)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) :
    Nonempty (CompletedScope c owner omitted palette) := by
  have hupper := fourColor_colorDegree_le_sixteen c hc omitted owner
  have hcases : colorDegree c omitted owner = 15 ∨ colorDegree c omitted owner = 16 := by omega
  rcases hcases with h | h
  · obtain ⟨t,⟨m⟩⟩ := fixed_palette_k15 c hc owner omitted h palette
    exact ⟨completed_from_k15 c owner omitted palette t m⟩
  · obtain ⟨t,⟨m⟩⟩ := fixed_palette_k16 c hc owner omitted h palette
    exact ⟨completed_from_k16 c owner omitted palette t m⟩

#print axioms high_neighborhood_completion
#print axioms fixed_palette_k16
#print axioms fixed_palette_k15
end PricingC
