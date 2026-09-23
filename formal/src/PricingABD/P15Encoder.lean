import PricingABD.TTExchange
import R4333Lean.FiniteColorCNF

namespace PricingABD.P15Encoder
open Ramsey61 Ramsey61.CEncodingCore PricingABD.TTExchange
open R4333.FiniteColorCNF

noncomputable def paletteEquiv : Fin 4 ≃ FourColor := Equiv.ofBijective palette
  ⟨palette_injective,palette_surjective⟩

abbrev Index := Fin 4 ⊕ (Fin 15 ⊕ (Fin 15 ⊕ Fin 16))

def indexEquiv : Index ≃ Fin 50 :=
  (Equiv.sumCongr (Equiv.refl (Fin 4))
    ((Equiv.sumCongr (Equiv.refl (Fin 15)) finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def indexColor : Index → FourColor
  | .inl _ => palette 0
  | .inr (.inl _) => palette 1
  | .inr (.inr (.inl _)) => palette 2
  | .inr (.inr (.inr _)) => palette 3

def physical {c : Host} {t : Bool} (f : Frame c 4 t) : Index → Fin 61
  | .inl a => f.free a
  | .inr (.inl a) => f.left a
  | .inr (.inr (.inl a)) => f.right a
  | .inr (.inr (.inr a)) => f.marked a

theorem physical_spoke {c : Host} {t : Bool} (f : Frame c 4 t) (a : Index) :
    c f.root (physical f a) = indexColor a := by
  rcases a with a | a | a | a
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.free_mem a)).2
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.left_mem a)).2
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.right_mem a)).2
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.marked_mem a)).2

theorem physical_injective {c : Host} {t : Bool} (f : Frame c 4 t) :
    Function.Injective (physical f) := by
  intro a b hab
  have hs : indexColor a = indexColor b := by rw [←physical_spoke f a,hab,physical_spoke f b]
  rcases a with a | a | a | a <;> rcases b with b | b | b | b
  all_goals try {cases hs}
  · exact congrArg Sum.inl (f.free.injective hab)
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (f.left.injective hab)
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (f.right.injective hab)
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr x))) (f.marked.injective hab)

def physicalVertex {c : Host} {t : Bool} (f : Frame c 4 t) (a : Fin 50) : Fin 61 := physical f (indexEquiv.symm a)

theorem physicalVertex_injective {c : Host} {t : Bool} (f : Frame c 4 t) :
    Function.Injective (physicalVertex f) := (physical_injective f).comp indexEquiv.symm.injective

noncomputable def physicalColoring {c : Host} {t : Bool} (f : Frame c 4 t) :
    R4333.EdgeColoring (Fin 50) (Fin 4) where
  color a b := paletteEquiv.symm (c (physicalVertex f a) (physicalVertex f b))
  color_symm a b := congrArg paletteEquiv.symm (c.color_symm _ _)

theorem physicalColoring_good {c : Host} {t : Bool} (f : Frame c 4 t)
    (hc : NoMonochromaticTriangle c) : R4333.NoMonochromaticTriangle (physicalColoring f) := by
  intro a b d hdist hmono
  exact hc (physicalVertex f a) (physicalVertex f b) (physicalVertex f d)
    ⟨(physicalVertex_injective f).ne hdist.1,(physicalVertex_injective f).ne hdist.2.1,
      (physicalVertex_injective f).ne hdist.2.2⟩
    ⟨paletteEquiv.symm.injective hmono.1,paletteEquiv.symm.injective hmono.2⟩

def freeVertex (a : Fin 4) : Fin 50 := ⟨a.val,by omega⟩
def leftVertex (a : Fin 15) : Fin 50 := ⟨4+a.val,by omega⟩
def rightVertex (a : Fin 15) : Fin 50 := ⟨19+a.val,by omega⟩
def qVertex (a : Fin 16) : Fin 50 := ⟨34+a.val,by omega⟩

theorem physicalVertex_free {c : Host} {t : Bool} (f : Frame c 4 t) (a : Fin 4) :
    physicalVertex f (freeVertex a) = f.free a := by
  change physical f (indexEquiv.symm (indexEquiv (Sum.inl a))) = _
  simp only [Equiv.symm_apply_apply];rfl

theorem physicalVertex_left {c : Host} {t : Bool} (f : Frame c 4 t) (a : Fin 15) :
    physicalVertex f (leftVertex a) = f.left a := by
  change physical f (indexEquiv.symm (indexEquiv (Sum.inr (Sum.inl a)))) = _
  simp only [Equiv.symm_apply_apply];rfl

theorem physicalVertex_right {c : Host} {t : Bool} (f : Frame c 4 t) (a : Fin 15) :
    physicalVertex f (rightVertex a) = f.right a := by
  have hv : rightVertex a = indexEquiv (Sum.inr (Sum.inr (Sum.inl a))) := by
    apply Fin.ext
    change 19 + a.val = 4 + (15 + a.val)
    omega
  rw [hv]
  simp only [physicalVertex,Equiv.symm_apply_apply];rfl

theorem physicalVertex_q {c : Host} {t : Bool} (f : Frame c 4 t) (a : Fin 16) :
    physicalVertex f (qVertex a) = f.marked a := by
  have hv : qVertex a = indexEquiv (Sum.inr (Sum.inr (Sum.inr a))) := by
    apply Fin.ext
    change 34 + a.val = 4 + (15 + (15 + a.val))
    omega
  rw [hv]
  simp only [physicalVertex,Equiv.symm_apply_apply];rfl

/-- Signed atom numbering matches the sparse Python decoder (DIMACS adds1). -/
def positiveUnit (a b : Nat) (q : Fin 4) : Sat.Clause := [.pos (edgeAtom a b q.val)]
def negativeZeroUnit (a b : Nat) : Sat.Clause := [.neg (edgeAtom a b 0)]

def mColor : Fin 3 → Fin 4 := ![0,2,3]
def xColor : Fin 3 → Fin 4 := ![0,1,3]
def qColor (q : Fin 3) : Fin 4 := Fin.castLE (by decide) q

/-- The authoritative330positive unit clauses, in exact block and edge order. -/
def templateUnits (qtype : Bool) : Sat.Fmla :=
  (edges 15).map (fun e => positiveUnit (4+e.1) (4+e.2) (mColor (R4333.k15Twisted ⟨e.1%15,by omega⟩ ⟨e.2%15,by omega⟩))) ++
  (edges 15).map (fun e => positiveUnit (19+e.1) (19+e.2) (xColor (R4333.k15Twisted ⟨e.1%15,by omega⟩ ⟨e.2%15,by omega⟩))) ++
  (edges 16).map (fun e => positiveUnit (34+e.1) (34+e.2) (qColor (R4333.k16Template qtype ⟨e.1%16,by omega⟩ ⟨e.2%16,by omega⟩)))

def rootForbiddenUnits : Sat.Fmla := (edges 4).map fun e => negativeZeroUnit e.1 e.2

def baseFmla (qtype : Bool) : Sat.Fmla := goodColoringFmla 50 4 ++ templateUnits qtype ++ rootForbiddenUnits

/-- Public decoding bounds proved from the actual ordered-pair construction. -/
theorem mem_edges_bounds {n a b : Nat} (h : (a,b) ∈ edges n) : a < n ∧ b < n ∧ a < b := by
  simp only [edges,vertices,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq] at h
  obtain ⟨x,hx,y,⟨hy,hxy⟩,he⟩ := h
  cases he
  exact ⟨hx,hy,hxy⟩

theorem positiveUnit_satisfied {c : Host} {t : Bool} (f : Frame c 4 t)
    (a b : Fin 50) (q : Fin 4) (h : c (physicalVertex f a) (physicalVertex f b) = palette q) :
    (coloringValuation (physicalColoring f)).satisfies (positiveUnit a.val b.val q) := by
  apply satisfies_of_mem_holds _ (l := .pos (edgeAtom a.val b.val q.val)) (List.Mem.head _)
  change coloringValuation (physicalColoring f) (edgeAtom a.val b.val q.val)
  rw [coloringValuation_edgeAtom]
  change paletteEquiv.symm (c (physicalVertex f a) (physicalVertex f b)) = q
  rw [h]
  exact paletteEquiv.symm_apply_apply q

theorem palette_mColor (q : Fin 3) : palette (mColor q) = mPalette q := by fin_cases q <;> rfl
theorem palette_xColor (q : Fin 3) : palette (xColor q) = xPalette q := by fin_cases q <;> rfl

theorem frame_satisfies_templates {c : Host} {t : Bool} (f : Frame c 4 t) :
    (coloringValuation (physicalColoring f)).satisfies_fmla (templateUnits t) := by
  constructor
  intro clause hcl
  simp only [templateUnits,List.mem_append,List.mem_map] at hcl
  rcases hcl with (⟨⟨a,b⟩,hab,rfl⟩ | ⟨⟨a,b⟩,hab,rfl⟩) | ⟨⟨a,b⟩,hab,rfl⟩
  · obtain ⟨ha,hb,hlt⟩ := mem_edges_bounds hab
    let u : Fin 15 := ⟨a,ha⟩
    let v : Fin 15 := ⟨b,hb⟩
    have he : c (physicalVertex f (leftVertex u)) (physicalVertex f (leftVertex v)) =
        palette (mColor (R4333.k15Twisted u v)) := by
      rw [physicalVertex_left,physicalVertex_left,palette_mColor]
      exact f.left_edges u v (Fin.ne_of_lt hlt)
    have h := positiveUnit_satisfied f (leftVertex u) (leftVertex v) _ he
    simpa only [leftVertex,u,v,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using h
  · obtain ⟨ha,hb,hlt⟩ := mem_edges_bounds hab
    let u : Fin 15 := ⟨a,ha⟩
    let v : Fin 15 := ⟨b,hb⟩
    have he : c (physicalVertex f (rightVertex u)) (physicalVertex f (rightVertex v)) =
        palette (xColor (R4333.k15Twisted u v)) := by
      rw [physicalVertex_right,physicalVertex_right,palette_xColor]
      exact f.right_edges u v (Fin.ne_of_lt hlt)
    have h := positiveUnit_satisfied f (rightVertex u) (rightVertex v) _ he
    simpa only [rightVertex,u,v,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using h
  · obtain ⟨ha,hb,hlt⟩ := mem_edges_bounds hab
    let u : Fin 16 := ⟨a,ha⟩
    let v : Fin 16 := ⟨b,hb⟩
    have he : c (physicalVertex f (qVertex u)) (physicalVertex f (qVertex v)) =
        palette (qColor (R4333.k16Template t u v)) := by
      rw [physicalVertex_q,physicalVertex_q]
      exact f.marked_edges u v (Fin.ne_of_lt hlt)
    have h := positiveUnit_satisfied f (qVertex u) (qVertex v) _ he
    simpa only [qVertex,u,v,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using h

theorem frame_satisfies_root_forbidden {c : Host} {t : Bool} (f : Frame c 4 t)
    (hc : NoMonochromaticTriangle c) :
    (coloringValuation (physicalColoring f)).satisfies_fmla rootForbiddenUnits := by
  constructor
  intro clause hcl
  simp only [rootForbiddenUnits,List.mem_map] at hcl
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := hcl
  obtain ⟨ha,hb,hlt⟩ := mem_edges_bounds hab
  let u : Fin 4 := ⟨a,ha⟩
  let v : Fin 4 := ⟨b,hb⟩
  apply satisfies_of_mem_holds _ (l := .neg (edgeAtom a b 0)) (List.Mem.head _)
  change ¬coloringValuation (physicalColoring f) (edgeAtom (freeVertex u).val (freeVertex v).val (0 : Fin 4).val)
  rw [coloringValuation_edgeAtom]
  change paletteEquiv.symm (c (physicalVertex f (freeVertex u)) (physicalVertex f (freeVertex v))) ≠ 0
  rw [physicalVertex_free,physicalVertex_free]
  intro h
  have he : c (f.free u) (f.free v) = palette 0 := (Equiv.symm_apply_eq paletteEquiv).mp h
  exact neighborhood_avoids_own_color c hc (f.free_mem u) (f.free_mem v)
    (f.free.injective.ne (Fin.ne_of_lt hlt)) he

/-- Any actual normalized TT frame satisfies all87311clauses of the original
P15 base, with no support-cover, encoder-soundness or auxiliary-valuation premise. -/
theorem frame_satisfies_exact_P15_base {c : Host} {t : Bool} (f : Frame c 4 t)
    (hc : NoMonochromaticTriangle c) :
    (coloringValuation (physicalColoring f)).satisfies_fmla (baseFmla t) := by
  constructor
  intro clause hcl
  simp only [baseFmla,List.mem_append] at hcl
  rcases hcl with (hcl | hcl) | hcl
  · exact (coloring_satisfies_goodColoringFmla (physicalColoring f) (physicalColoring_good f hc)).prop clause hcl
  · exact (frame_satisfies_templates f).prop clause hcl
  · exact (frame_satisfies_root_forbidden f hc).prop clause hcl

#print axioms physicalColoring_good
#print axioms frame_satisfies_exact_P15_base
#check frame_satisfies_exact_P15_base
end PricingABD.P15Encoder
