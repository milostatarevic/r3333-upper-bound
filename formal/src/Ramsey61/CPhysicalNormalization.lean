import Ramsey61.CEncodingBase

namespace Ramsey61.CPhysicalNormalization
open Finset CEncodingCore CEncodingBase

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

theorem relabel_selector (c : Host) (h : SelectorX c) (e : Vertex ≃ Vertex)
    (σ : FourColor ≃ FourColor) : SelectorX (relabel c e σ) := by
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

/-- The canonical blocks of the unchanged Python encoder. -/
def canonicalCell (v : Vertex) : Option FourColor :=
  if v = 0 then none else if v.val ≤ 16 then some (palette 0)
  else if v.val ≤ 32 then some (palette 1)
  else if v.val ≤ 46 then some (palette 2) else some (palette 3)

def rootCell (c : Host) (r : Vertex) (σ : FourColor ≃ FourColor) (v : Vertex) : Option FourColor :=
  if v = r then none else some (σ.symm (c r v))

@[simp] theorem rootCell_none (c : Host) (r v : Vertex) (σ : FourColor ≃ FourColor) :
    rootCell c r σ v = none ↔ v = r := by simp [rootCell]

theorem rootCell_some (c : Host) (r v : Vertex) (σ : FourColor ≃ FourColor) (q : FourColor) :
    rootCell c r σ v = some q ↔ v ∈ colorNeighborhood c (σ q) r := by
  simp [rootCell,mem_colorNeighborhood,Equiv.symm_apply_eq]

set_option maxRecDepth 10000 in
theorem canonicalCell_none : ∀ v, canonicalCell v = none ↔ v = 0 := by decide

set_option maxRecDepth 10000 in
theorem canonicalCell_blocks : ∀ q v, v ∈ rootBlocks q → canonicalCell v = some (palette q) := by decide

set_option maxRecDepth 10000 in
theorem canonicalCell_card : ∀ q,
    Fintype.card {v // canonicalCell v = some (palette q)} = if q.val < 2 then 16 else 14 := by decide

theorem rootCell_card (c : Host) (r : Vertex) (σ : FourColor ≃ FourColor) (q : FourColor) :
    Fintype.card {v // rootCell c r σ v = some q} = colorDegree c (σ q) r := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext v
  simp [rootCell_some]

/-- Equal physical root-cell sizes construct a single simultaneous vertex bijection. -/
theorem exists_root_cell_equiv (c : Host) (r : Vertex) (σ : FourColor ≃ FourColor)
    (hd : ∀ q : Color, colorDegree c (σ (palette q)) r = if q.val < 2 then 16 else 14) :
    ∃ e : Vertex ≃ Vertex, e 0 = r ∧ ∀ v, rootCell c r σ (e v) = canonicalCell v := by
  have hcards : ∀ k, Fintype.card {v // canonicalCell v = k} =
      Fintype.card {v // rootCell c r σ v = k} := by
    intro k
    cases k with
    | none => simp only [canonicalCell_none,rootCell_none]; simp
    | some q =>
      obtain ⟨q,rfl⟩ := palette_surjective q
      rw [rootCell_card,canonicalCell_card,hd]
  obtain ⟨e,he⟩ := exists_equiv_of_fiber_card canonicalCell (rootCell c r σ) hcards
  refine ⟨e,?_,he⟩
  exact (rootCell_none c r (e 0) σ).mp (by rw [he]; rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- The finite palette choice retains the distinguished joining color at index2. -/
theorem palette_order_table : ∀ (high : FourColor → Bool) (marked : FourColor),
    high marked = false → ((Finset.univ : Finset FourColor).filter fun q => high q).card = 2 →
    ∃ σ : Equiv.Perm FourColor, σ (palette 2) = marked ∧
      ∀ q : Color, high (σ (palette q)) = decide (q.val < 2) := by decide

theorem exists_ordered_palette (c : Host) (hc : NoMonochromaticTriangle c) (r : Vertex)
    (hm : W c r = 32) (marked : FourColor) (hlow : colorDegree c marked r < 15) :
    ∃ σ : Equiv.Perm FourColor, σ (palette 2) = marked ∧
      ∀ q : Color, colorDegree c (σ (palette q)) r = if q.val < 2 then 16 else 14 := by
  classical
  have hd := W32_degree_cases c hc r hm
  let high : FourColor → Bool := fun q => decide (colorDegree c q r = 16)
  have hmarked : high marked = false := by simp [high]; omega
  have hterm (q : FourColor) :
      (if 15 ≤ colorDegree c q r then colorDegree c q r else 0) =
      if high q then 16 else 0 := by
    rcases hd q with h | h <;> simp [high,h]
  have hcard : ((Finset.univ : Finset FourColor).filter fun q => high q).card = 2 := by
    change (∑ q : FourColor, if 15 ≤ colorDegree c q r then colorDegree c q r else 0) = 32 at hm
    simp only [hterm] at hm
    rw [←Finset.sum_filter] at hm
    simp only [Finset.sum_const,Nat.nsmul_eq_mul] at hm
    omega
  obtain ⟨σ,hσ,hh⟩ := palette_order_table high marked hmarked hcard
  refine ⟨σ,hσ,?_⟩
  intro q
  have ht := hh q
  rcases hd (σ (palette q)) with h | h
  · simp only [high,h,show ¬(14:Nat)=16 by decide,decide_false,Bool.false_eq] at ht
    simp [h,show ¬q.val<2 by simpa using ht]
  · simp only [high,h,decide_true,Bool.true_eq] at ht
    simp [h,show q.val<2 by simpa using ht]

/-- Swapping equal-label vertices preserves every physical cell. -/
theorem swap_preserves_label {α β : Type*} [DecidableEq α] (f : α → β)
    (a b : α) (h : f a = f b) (x : α) : f (Equiv.swap a b x) = f x := by
  by_cases hxa : x = a
  · subst x; simpa using h.symm
  by_cases hxb : x = b
  · subst x; simpa using h
  simp [Equiv.swap_apply_def,hxa,hxb]

theorem exists_marked_root_cell_equiv (c : Host) (r u : Vertex) (hne : u ≠ r)
    (σ : FourColor ≃ FourColor) (hmarked : σ (palette 2) = c r u)
    (hd : ∀ q : Color, colorDegree c (σ (palette q)) r = if q.val < 2 then 16 else 14) :
    ∃ e : Vertex ≃ Vertex, e 0 = r ∧ e 33 = u ∧
      ∀ v, rootCell c r σ (e v) = canonicalCell v := by
  obtain ⟨e,he0,he⟩ := exists_root_cell_equiv c r σ hd
  have hu : rootCell c r σ u = some (palette 2) := by
    apply (rootCell_some c r u σ (palette 2)).mpr
    exact (mem_colorNeighborhood c _ _ _).mpr ⟨hne,hmarked.symm⟩
  have h33 : canonicalCell (33 : Vertex) = some (palette 2) := by decide
  have he33 : e 33 ≠ r := by
    intro h
    have : (33 : Vertex) = 0 := e.injective (h.trans he0.symm)
    exact (by decide : (33 : Vertex) ≠ 0) this
  let swap := Equiv.swap (e 33) u
  refine ⟨e.trans swap,?_,by simp [swap],?_⟩
  · simp [swap,he0,Equiv.swap_apply_def,he33.symm,hne.symm]
  · intro v
    rw [Equiv.trans_apply,swap_preserves_label (rootCell c r σ) (e 33) u (by rw [he,h33,hu])]
    exact he v

/-- Complete physical entrance normalization: one vertex permutation, one global
palette permutation, root0, the marked neighbor33, and the unchanged base's
16/16/14/14 blocks. No separate neighborhood recoloring is used. -/
theorem exterior_witness_normalized (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (witness : CExteriorWitness c) :
    ∃ (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor),
      NoMonochromaticTriangle (relabel c e σ) ∧ SelectorX (relabel c e σ) ∧
      RootConditions (relabel c e σ) ∧
      15 ≤ colorDegree (relabel c e σ) (palette 2) 33 := by
  obtain ⟨r,u,hm,hh,hu,hnot⟩ := witness
  obtain ⟨hne,hlow,hhigh⟩ := (witness_edge_semantics c r u).mp ⟨hu,hnot⟩
  obtain ⟨σ,hσ,hd⟩ := exists_ordered_palette c hc r hm (c r u) hlow
  obtain ⟨e,he0,he33,he⟩ := exists_marked_root_cell_equiv c r u hne σ hσ hd
  refine ⟨e,σ,relabel_noMono c hc e σ,relabel_selector c selectors e σ,?_,?_⟩
  · constructor
    · intro q v hv
      have hvcell := (rootCell_some c r (e v) σ (palette q)).mp
        ((he v).trans (canonicalCell_blocks q v hv))
      have hcolor := (mem_colorNeighborhood c _ _ _).mp hvcell
      change σ.symm (c (e 0) (e v)) = palette q
      rw [he0,hcolor.2,σ.symm_apply_apply]
    · simpa only [relabel_H,he0] using hh
  · simpa only [relabel_degree,he33,hσ] using hhigh

/-- The physical entrance supplies the same normalized coloring to every base
clause. Additional seed clauses must preserve these simultaneous maps. -/
theorem exterior_witness_supplies_base (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (witness : CExteriorWitness c) :
    ∃ (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor),
      NoMonochromaticTriangle (relabel c e σ) ∧ SelectorX (relabel c e σ) ∧
      RootConditions (relabel c e σ) ∧
      15 ≤ colorDegree (relabel c e σ) (palette 2) 33 ∧
      DenseCounter.FormulaSat (baseValuation (relabel c e σ)) broaderBaseCNF := by
  obtain ⟨e,σ,hgood,hselector,hroot,hmarked⟩ := exterior_witness_normalized c hc selectors witness
  exact ⟨e,σ,hgood,hselector,hroot,hmarked,
    coloring_satisfies_broaderBase (relabel c e σ) hgood hselector hroot⟩


end Ramsey61.CPhysicalNormalization
