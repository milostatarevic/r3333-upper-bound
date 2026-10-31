import UniformK60.Physical
import UniformK60.Selector

/-! A single physical vertex bijection and global color permutation for K60.
Root layouts are arbitrary partitions, so the same theorem handles all six
profiles without adding vertices or prescribing unobserved edges. -/
set_option autoImplicit false
namespace UniformK60.HostNormalization
open Ramsey61 Finset UniformK60.Physical

/-- One simultaneous physical vertex bijection and one global palette permutation. -/
def relabel (c : Host) (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor) : Host where
  color x y := σ.symm (c (e x) (e y))
  color_symm x y := congrArg σ.symm (c.color_symm (e x) (e y))

theorem relabel_noMono (c : Host) (hc : NoMonochromaticTriangle c)
    (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor) :
    NoMonochromaticTriangle (relabel c e σ) := by
  intro x y z hd ht
  apply hc (e x) (e y) (e z)
    ⟨fun h => hd.1 (e.injective h),fun h => hd.2.1 (e.injective h),
      fun h => hd.2.2 (e.injective h)⟩
  exact ⟨σ.symm.injective ht.1,σ.symm.injective ht.2⟩

theorem relabel_degree (c : Host) (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor)
    (q : FourColor) (v : Vertex) :
    colorDegree (relabel c e σ) q v = colorDegree c (σ q) (e v) := by
  unfold colorDegree
  apply Finset.card_bij (fun u _ => e u)
  · intro u hu
    simpa [mem_colorNeighborhood,relabel,Equiv.symm_apply_eq] using hu
  · intro u hu w hw h; exact e.injective h
  · intro u hu
    refine ⟨e.symm u,?_,by simp⟩
    simpa [mem_colorNeighborhood,relabel,Equiv.symm_apply_eq] using hu

theorem relabel_H (c : Host) (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor)
    (v : Vertex) : H (relabel c e σ) v = H c (e v) := by
  unfold H highOwnNeighborCount
  apply Finset.card_bij (fun u _ => e u)
  · intro u hu
    simp only [mem_highOwnNeighborSupport,relabel_degree] at hu ⊢
    simpa [relabel,Equiv.symm_apply_eq] using hu
  · intro u hu w hw h; exact e.injective h
  · intro u hu
    refine ⟨e.symm u,?_,by simp⟩
    simp only [mem_highOwnNeighborSupport,relabel_degree]
    simpa [relabel,Equiv.symm_apply_eq] using hu

theorem relabel_W (c : Host) (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor)
    (v : Vertex) : W (relabel c e σ) v = W c (e v) := by
  unfold W criticalDegreeMass
  simp only [relabel_degree]
  exact Equiv.sum_comp σ (fun q => if 15 ≤ colorDegree c q (e v) then colorDegree c q (e v) else 0)

theorem relabel_selector (c : Host) (h : StrictTicketBounds c) (e : Vertex ≃ Vertex)
    (σ : FourColor ≃ FourColor) : StrictTicketBounds (relabel c e σ) := by
  intro v
  simpa only [relabel_W,relabel_H] using h (e v)

/-- A finite partition isomorphism is constructed from equal fiber cardinalities. -/
theorem exists_equiv_of_fiber_card {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq γ] (f : α → γ) (g : β → γ)
    (h : ∀ k, Fintype.card {a // f a = k} = Fintype.card {b // g b = k}) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  let es (k : γ) : {a // f a = k} ≃ {b // g b = k} := Fintype.equivOfCardEq (h k)
  exact ⟨Equiv.ofFiberEquiv es,Equiv.ofFiberEquiv_map es⟩

def rootCell (c : Host) (r : Vertex) (σ : FourColor ≃ FourColor) (v : Vertex) : Option FourColor :=
  if v = r then none else some (σ.symm (c r v))

@[simp] theorem rootCell_none (c : Host) (r v : Vertex) (σ : FourColor ≃ FourColor) :
    rootCell c r σ v = none ↔ v = r := by simp [rootCell]

theorem rootCell_some (c : Host) (r v : Vertex) (σ : FourColor ≃ FourColor) (q : FourColor) :
    rootCell c r σ v = some q ↔ v ∈ colorNeighborhood c (σ q) r := by
  simp [rootCell,mem_colorNeighborhood,Equiv.symm_apply_eq]

theorem rootCell_card (c : Host) (r : Vertex) (σ : FourColor ≃ FourColor) (q : FourColor) :
    Fintype.card {v // rootCell c r σ v = some q} = colorDegree c (σ q) r := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext v
  simp [rootCell_some]


/-- Equal root-cell cardinalities normalize any specified K60 layout. -/
theorem exists_root_cell_equiv (c : Host) (r : Vertex) (σ : FourColor ≃ FourColor)
    (cell : Vertex → Option FourColor)
    (hzero : ∀ v, cell v = none ↔ v = 0)
    (hd : ∀ q : FourColor,
      Fintype.card {v // cell v = some q} = colorDegree c (σ q) r) :
    ∃ e : Vertex ≃ Vertex, e 0 = r ∧ ∀ v, rootCell c r σ (e v) = cell v := by
  classical
  have hcards : ∀ k, Fintype.card {v // cell v = k} =
      Fintype.card {v // rootCell c r σ v = k} := by
    intro k
    cases k with
    | none => simp only [hzero, rootCell_none]; simp
    | some q => rw [rootCell_card, hd]
  obtain ⟨e, he⟩ := exists_equiv_of_fiber_card cell (rootCell c r σ) hcards
  refine ⟨e, ?_, he⟩
  exact (rootCell_none c r (e 0) σ).mp (by rw [he]; exact (hzero 0).mpr rfl)

/-- The root-cell map fixes every physical root spoke in the normalized host. -/
theorem relabel_root_spoke (c : Host) (r : Vertex) (σ : FourColor ≃ FourColor)
    (cell : Vertex → Option FourColor) (e : Vertex ≃ Vertex)
    (he0 : e 0 = r) (he : ∀ v, rootCell c r σ (e v) = cell v)
    (v : Vertex) (q : FourColor) (hv : cell v = some q) :
    relabel c e σ 0 v = q := by
  have hm := (rootCell_some c r (e v) σ q).mp ((he v).trans hv)
  have hcolor := (mem_colorNeighborhood c (σ q) r (e v)).mp hm |>.2
  change σ.symm (c (e 0) (e v)) = q
  rw [he0, hcolor, Equiv.symm_apply_apply]

@[simp] theorem relabel_critical_mem (c : Host) (e : Vertex ≃ Vertex)
    (σ : FourColor ≃ FourColor) (v : Vertex) (q : FourColor) :
    q ∈ criticalColors (relabel c e σ) v ↔ σ q ∈ criticalColors c (e v) := by
  simp only [mem_criticalColors, relabel_degree]

/-- Swapping equal-label vertices preserves every physical cell. -/
theorem swap_preserves_label {α β : Type*} [DecidableEq α] (f : α → β)
    (a b : α) (h : f a = f b) (x : α) : f (Equiv.swap a b x) = f x := by
  by_cases hxa : x = a
  · subst x; simpa using h.symm
  by_cases hxb : x = b
  · subst x; simpa using h
  simp [Equiv.swap_apply_def,hxa,hxb]


#print axioms relabel_noMono
#print axioms relabel_degree
#print axioms exists_root_cell_equiv
end UniformK60.HostNormalization
