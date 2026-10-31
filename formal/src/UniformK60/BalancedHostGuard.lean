import UniformK60.BalancedHostVisible
import UniformK60.BalancedAnchorSupport
import UniformK60.BalancedEncodingGuard
import UniformK60.ClassificationFiberOrders

/-! Actual4/5 cross-guards in either canonical balanced root layout. The P4
case is obtained from classification of the entire attaching neighborhood. -/
set_option autoImplicit false
namespace UniformK60.BalancedHost
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.HostNormalization UniformK60.ClassificationGeometry
open UniformK60.ClassificationFiberOrders UniformK60.ClassificationSupportOrders

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_other : ∀ (c1 : Bool) (s : Scope c1) (v : Vertex),
    canonicalCell c1 v = some (palette (oppositeColor s)) ↔
      ∃ m : Fin (otherSize s), otherVertex s m = v := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_center : ∀ (c1 : Bool) (s : Scope c1),
    canonicalCell c1 (centerVertex s) = some (palette (ownColor s)) := by decide +kernel

theorem center_mem {c1 : Bool} {c : Host} (h : Spokes c1 c) (s : Scope c1) :
    centerVertex s ∈ colorNeighborhood c (palette (ownColor s)) 0 := by
  apply (rootCell_some c 0 _ (Equiv.refl _) _).mp
  rw [h,canonical_center]
  rfl

theorem root_mem {c1 : Bool} {c : Host} (h : Spokes c1 c) (s : Scope c1) :
    (0 : Vertex) ∈ colorNeighborhood c (palette (ownColor s)) (centerVertex s) := by
  obtain ⟨hne,hc⟩ := (mem_colorNeighborhood _ _ _ _).mp (center_mem h s)
  exact (mem_colorNeighborhood _ _ _ _).mpr ⟨hne.symm,by rw [c.color_symm];exact hc⟩

theorem other_mem_iff {c1 : Bool} {c : Host} (h : Spokes c1 c) (s : Scope c1) (v : Vertex) :
    v ∈ colorNeighborhood c (palette (oppositeColor s)) 0 ↔
      ∃ m : Fin (otherSize s), otherVertex s m = v := by
  have hh := rootCell_some c 0 v (Equiv.refl _) (palette (oppositeColor s))
  simp only [Equiv.refl_apply] at hh
  rw [←hh,h,canonical_other]

def guardSet {c1 : Bool} (c : Host) (s : Scope c1) : Finset (Fin (otherSize s)) :=
  univ.filter fun m => c (centerVertex s) (otherVertex s m) = palette (ownColor s)

def castSet {c1 : Bool} (c : Host) (s : Scope c1) : Finset (Fin 16) :=
  (guardSet c s).image (Fin.castLE (other_le s))

def guardMinor {c1 : Bool} (s : Scope c1) : Bool := decide (otherSize s = 15)

theorem cast_injective {c1 : Bool} (s : Scope c1) : Function.Injective (Fin.castLE (other_le s)) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem cast_mem {c1 : Bool} (c : Host) (s : Scope c1) (m : Fin (otherSize s)) :
    Fin.castLE (other_le s) m ∈ castSet c s ↔ m ∈ guardSet c s := by
  simp only [castSet,Finset.mem_image]
  constructor
  · rintro ⟨a,ha,he⟩
    exact (cast_injective s he) ▸ ha
  · intro h
    exact ⟨m,h,rfl⟩

theorem guard_image {c1 : Bool} {c : Host} (h : Spokes c1 c) (s : Scope c1) :
    (guardSet c s).image (otherVertex s) =
      attachingSupport c 0 (palette (ownColor s)) (centerVertex s) (palette (oppositeColor s)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hv
    apply mem_inter.mpr
    refine ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨(own_other_ne s _ _).symm,?_⟩,
      (other_mem_iff h s _).mpr ⟨m,rfl⟩⟩
    simpa only [guardSet,mem_filter,mem_univ,true_and] using hm
  · intro hv
    obtain ⟨hmark,hroot⟩ := mem_inter.mp hv
    obtain ⟨m,rfl⟩ := (other_mem_iff h s v).mp hroot
    exact mem_image.mpr ⟨m,by simpa only [guardSet,mem_filter,mem_univ,true_and]
      using ((mem_colorNeighborhood _ _ _ _).mp hmark).2,rfl⟩

theorem guard_card {c1 : Bool} {c : Host} (h : Spokes c1 c) (s : Scope c1) :
    (castSet c s).card =
      (attachingSupport c 0 (palette (ownColor s)) (centerVertex s) (palette (oppositeColor s))).card := by
  rw [castSet,card_image_of_injective _ (cast_injective s),←guard_image h s,
    card_image_of_injective _ (other_injective s)]

theorem guard_valid {c1 : Bool} (c : Host) (s : Scope c1) :
    ∀ v ∈ castSet c s, BalancedAnchor.validPosition (guardMinor s) v := by
  intro v hv
  obtain ⟨m,hm,rfl⟩ := mem_image.mp hv
  have bound := m.isLt
  cases c1 <;> cases s <;>
    simp_all [otherSize,guardMinor,firstSize,BalancedAnchor.validPosition]

theorem other_zero {c1 : Bool} (s : Scope c1) : foreign (oppositeColor s) 0 = ownColor s := by
  cases s <;> rfl

theorem other_one {c1 : Bool} (s : Scope c1) : foreign (oppositeColor s) 1 = 2 := by
  cases s <;> rfl

theorem guard_independent {c1 : Bool} {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized c1 c o) (s : Scope c1) :
    UniformK61.BalancedAnchor.Independent (otherKind o s) (castSet c s) := by
  intro a ha b hb hab he
  obtain ⟨a,haa,rfl⟩ := mem_image.mp ha
  obtain ⟨b,hbb,rfl⟩ := mem_image.mp hb
  have ha' : c (centerVertex s) (otherVertex s a) = palette (ownColor s) := by
    simpa only [guardSet,mem_filter,mem_univ,true_and] using haa
  have hb' : c (centerVertex s) (otherVertex s b) = palette (ownColor s) := by
    simpa only [guardSet,mem_filter,mem_univ,true_and] using hbb
  have hab' : a ≠ b := by intro h;subst b;exact hab rfl
  have hedge := other_template hn s a b hab'
  rw [he,other_zero] at hedge
  exact hc _ _ _ ⟨own_other_ne s _ _,own_other_ne s _ _,(other_injective s).ne hab'⟩
    ⟨ha'.trans hb'.symm,hb'.trans hedge.symm⟩

/-- Exact physical P4/C5 geometry follows from the actual critical
neighborhood of the center, not from an arbitrary independent4-set. -/
theorem guard_ordered {c1 : Bool} {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized c1 c o) (s : Scope c1) :
    ((castSet c s).card = 4 ∧
      ∃ e : Fin 4 ↪ Vertex,
        univ.image e = attachingSupport c 0 (palette (ownColor s)) (centerVertex s) (palette (oppositeColor s)) ∧
        ∀ i j, i ≠ j → (c (e i) (e j) = palette 2 ↔ PathAdjacent i j)) ∨
    (castSet c s).card = 5 := by
  have hhigh := named_high c hn.caps (centerVertex s) (ownColor s) (by cases s <;> simp only [ownColor] <;> decide)
  have hcolors : palette (oppositeColor s) ≠ palette (ownColor s) ∧
      palette 2 ≠ palette (ownColor s) ∧ palette 2 ≠ palette (oppositeColor s) := by
    cases s <;> simp only [ownColor,oppositeColor] <;> decide
  have h := physical_fiber_ordered c hc (centerVertex s) 0 (palette (ownColor s))
    (root_mem hn.spokes s) hhigh (palette (oppositeColor s)) (palette 2)
    hcolors.1 hcolors.2.1 hcolors.2.2
  rw [guard_card hn.spokes s]
  rcases h with ⟨h4,e,he,hp⟩ | ⟨h5,e,he,hp⟩
  · exact Or.inl ⟨h4,e,he,hp⟩
  · exact Or.inr h5

theorem guard_path_pattern {c1 : Bool} {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized c1 c o) (s : Scope c1)
    (e : Fin 4 ↪ Vertex)
    (he : univ.image e = attachingSupport c 0 (palette (ownColor s)) (centerVertex s) (palette (oppositeColor s)))
    (hp : ∀ i j, i ≠ j → (c (e i) (e j) = palette 2 ↔ PathAdjacent i j)) :
    ∃ i : BalancedAnchor.PatternIndex (guardMinor s) (otherKind o s),
      BalancedAnchor.pattern (guardMinor s) (otherKind o s) i = castSet c s := by
  classical
  have hem (i : Fin 4) : e i ∈ attachingSupport c 0 (palette (ownColor s)) (centerVertex s) (palette (oppositeColor s)) := by
    rw [←he]
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have hex (i : Fin 4) : ∃ m : Fin (otherSize s), otherVertex s m = e i :=
    (other_mem_iff hn.spokes s _).mp (mem_inter.mp (hem i)).2
  let pos : Fin 4 → Fin (otherSize s) := fun i => Classical.choose (hex i)
  have hpos (i : Fin 4) : otherVertex s (pos i) = e i := Classical.choose_spec (hex i)
  have posinj : Function.Injective pos := by
    intro i j hij
    apply e.injective
    exact (hpos i).symm.trans ((congrArg (otherVertex s) hij).trans (hpos j))
  let coords : Fin 4 → Fin 16 := fun i => Fin.castLE (other_le s) (pos i)
  have coordsinj : Function.Injective coords := (cast_injective s).comp posinj
  have posmem (i : Fin 4) : pos i ∈ guardSet c s := by
    simp only [guardSet,mem_filter,mem_univ,true_and]
    rw [hpos]
    exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp (hem i)).1).2
  have coordsmem (i : Fin 4) : coords i ∈ castSet c s := (cast_mem c s _).mpr (posmem i)
  have image : univ.image coords = castSet c s := by
    ext a
    constructor
    · rintro ha
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      exact coordsmem i
    · intro ha
      obtain ⟨m,hm,rfl⟩ := mem_image.mp ha
      have hphysical : otherVertex s m ∈ attachingSupport c 0 (palette (ownColor s)) (centerVertex s) (palette (oppositeColor s)) := by
        rw [←guard_image hn.spokes s]
        exact mem_image.mpr ⟨m,hm,rfl⟩
      rw [←he] at hphysical
      obtain ⟨i,_,hi⟩ := mem_image.mp hphysical
      have hmi : pos i = m := other_injective s ((hpos i).trans hi)
      exact mem_image.mpr ⟨i,mem_univ _,congrArg (Fin.castLE (other_le s)) hmi⟩
  have colors (i j : Fin 4) (hij : i ≠ j) :
      R4333.k16Template (otherKind o s) (coords i) (coords j) =
        if PathAdjacent i j then 1 else 2 := by
    have hedge := other_template hn s (pos i) (pos j) (posinj.ne hij)
    rw [hpos,hpos] at hedge
    change c (e i) (e j) = palette (foreign (oppositeColor s)
      (R4333.k16Template (otherKind o s) (coords i) (coords j))) at hedge
    have hzero := guard_independent hc hn s _ (coordsmem i) _ (coordsmem j) (coordsinj.ne hij)
    by_cases hadj : PathAdjacent i j
    · have hphysical := (hp i j hij).mpr hadj
      have hone : palette (foreign (oppositeColor s)
          (R4333.k16Template (otherKind o s) (coords i) (coords j))) =
          palette (foreign (oppositeColor s) 1) := by
        rw [other_one]
        exact hedge.symm.trans hphysical
      simpa only [if_pos hadj] using
        BalancedEncoding.foreign_injective _ (palette_injective hone)
    · have hone : R4333.k16Template (otherKind o s) (coords i) (coords j) ≠ 1 := by
        intro h
        rw [h,other_one] at hedge
        exact hadj ((hp i j hij).mp hedge)
      have htwo : R4333.k16Template (otherKind o s) (coords i) (coords j) = 2 := by
        have hlt := (R4333.k16Template (otherKind o s) (coords i) (coords j)).isLt
        apply Fin.ext
        have h0 : (R4333.k16Template (otherKind o s) (coords i) (coords j)).val ≠ 0 := by
          intro h;exact hzero (Fin.ext h)
        have h1 : (R4333.k16Template (otherKind o s) (coords i) (coords j)).val ≠ 1 := by
          intro h;exact hone (Fin.ext h)
        omega
      simpa only [if_neg hadj] using htwo
  have valid (i : Fin 4) := guard_valid c s _ (coordsmem i)
  have h01 : R4333.k16Template (otherKind o s) (coords 0) (coords 1) = 1 := by
    simpa [PathAdjacent] using colors 0 1 (by decide)
  have h02 : R4333.k16Template (otherKind o s) (coords 0) (coords 2) = 2 := by
    simpa [PathAdjacent] using colors 0 2 (by decide)
  have h12 : R4333.k16Template (otherKind o s) (coords 1) (coords 2) = 1 := by
    simpa [PathAdjacent] using colors 1 2 (by decide)
  have h03 : R4333.k16Template (otherKind o s) (coords 0) (coords 3) = 2 := by
    simpa [PathAdjacent] using colors 0 3 (by decide)
  have h13 : R4333.k16Template (otherKind o s) (coords 1) (coords 3) = 2 := by
    simpa [PathAdjacent] using colors 1 3 (by decide)
  have h23 : R4333.k16Template (otherKind o s) (coords 2) (coords 3) = 1 := by
    simpa [PathAdjacent] using colors 2 3 (by decide)
  obtain ⟨i,hi⟩ := BalancedAnchor.p4_complete (guardMinor s) (otherKind o s)
    (coords 0) (valid 0) (coords 1) (valid 1) h01 (coords 2) (valid 2) h02 h12
    (coords 3) (valid 3) h03 h13 h23
  refine ⟨i,hi.trans ?_⟩
  have hu : (univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  simpa only [hu,image_insert,image_singleton] using image

/-- Exact selector coverage for every actual cross-guard in either layout. -/
theorem actual_guard_pattern {c1 : Bool} {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized c1 c o) (s : Scope c1) :
    ∃ i : BalancedAnchor.PatternIndex (guardMinor s) (otherKind o s),
      BalancedAnchor.pattern (guardMinor s) (otherKind o s) i = castSet c s := by
  rcases guard_ordered hc hn s with ⟨_,e,he,hp⟩ | h5
  · exact guard_path_pattern hc hn s e he hp
  · exact BalancedAnchor.c5_complete _ _ _ h5 (guard_independent hc hn s) (guard_valid c s)

#print axioms actual_guard_pattern
end UniformK60.BalancedHost
