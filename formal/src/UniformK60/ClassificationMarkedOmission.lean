import UniformK60.ClassificationMarks

set_option autoImplicit false
namespace UniformK60.ClassificationMarkedOmission
open Ramsey61 Finset UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette
open UniformK60.ClassificationMarks

/-- A color-preserving full-template coordinate change sends the actual mark
onto position15 and the absent position onto a retained omission representative. -/
def orient (t : Bool) (mark : Fin 15) : Fin 16 → Fin 16 :=
  if t then (![![15,7,4,12,2,10,9,1,14,6,5,13,3,11,8,0],![14,15,12,13,10,11,8,9,6,7,4,5,2,3,0,1],![13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2],![12,13,14,15,11,10,9,8,4,5,6,7,3,2,1,0],![8,9,10,11,15,14,13,12,0,1,2,3,7,6,5,4],![9,1,2,10,7,15,12,4,8,0,3,11,6,14,13,5],![9,8,11,10,13,12,15,14,1,0,3,2,5,4,7,6],![11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7],![14,6,5,13,0,8,11,3,15,7,4,12,1,9,10,2],![6,14,13,5,11,3,0,8,7,15,12,4,10,2,1,9],![5,4,7,6,2,3,0,1,13,12,15,14,10,11,8,9],![13,5,6,14,3,11,8,0,12,4,7,15,2,10,9,1],![0,8,11,3,14,6,5,13,1,9,10,2,15,7,4,12],![11,3,0,8,6,14,13,5,10,2,1,9,7,15,12,4],![8,0,3,11,5,13,14,6,9,1,2,10,4,12,15,7]] : Fin 15 → Fin 16 → Fin 16) mark
  else (![![15,5,2,8,11,1,6,12,3,9,14,4,7,13,10,0],![0,15,2,13,6,9,4,11,10,5,8,7,12,3,14,1],![8,4,15,3,1,13,6,10,0,12,7,11,9,5,14,2],![8,4,3,15,13,1,6,10,2,14,9,5,7,11,12,0],![10,6,1,13,15,3,4,8,0,12,11,7,5,9,14,2],![1,9,2,10,7,15,4,12,13,5,14,6,11,3,8,0],![9,8,10,11,12,13,15,14,6,7,5,4,3,2,0,1],![8,9,11,10,13,12,14,15,7,6,4,5,2,3,1,0],![3,11,0,8,5,13,6,14,15,7,12,4,9,1,10,2],![9,5,2,14,12,0,7,11,3,15,8,4,6,10,13,1],![0,8,3,11,6,14,5,13,12,4,15,7,10,2,9,1],![13,5,6,14,3,11,8,0,12,4,7,15,2,10,9,1],![3,12,1,14,5,10,7,8,9,6,11,4,15,0,13,2],![8,7,5,10,1,14,12,3,9,6,4,11,0,15,13,2],![1,14,3,12,7,8,5,10,11,4,9,6,13,2,15,0]] : Fin 15 → Fin 16 → Fin 16) mark

set_option maxRecDepth 100000 in
theorem orient_bijective : ∀ t i, Function.Bijective (orient t i) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem orient_preserves : ∀ t i a b, a ≠ b →
    R4333.k16Template t (orient t i a) (orient t i b) = R4333.k16Template t a b := by
  decide

theorem orient_mark : ∀ t i, orient t i i.castSucc = 15 := by decide

theorem orient_missing : ∀ t i,
    orient t i 15 = (markRepresentative t i).castSucc := by decide

noncomputable def orientEquiv (t : Bool) (i : Fin 15) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (orient t i) (orient_bijective t i)

abbrev Surviving (r : Fin 15) := {j : Fin 16 // j ≠ r.castSucc}

def markPosition (r : Fin 15) : Surviving r := ⟨15, by
  intro h; have hv : (15 : Nat)=r.val := congrArg (fun x : Fin 16 => x.val) h
  have := r.isLt; omega⟩

noncomputable def omissionEquiv (t : Bool) (i : Fin 15) :
    Fin 15 ≃ Surviving (markRepresentative t i) := by
  let e := orientEquiv t i
  have h15 : e 15 = (markRepresentative t i).castSucc := orient_missing t i
  let f : Fin 15 → Surviving (markRepresentative t i) := fun j =>
    ⟨e j.castSucc, by
      intro h
      have he : j.castSucc = (15 : Fin 16) := e.injective (h.trans h15.symm)
      have hv : j.val=15 := congrArg (fun x : Fin 16 => x.val) he
      have := j.isLt; omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin 16 => x.val) (e.injective (congrArg Subtype.val h))
  · intro j
    have hne : e.symm j.val ≠ (15 : Fin 16) := by
      intro h
      apply j.property
      calc j.val = e (e.symm j.val) := (e.apply_symm_apply j.val).symm
           _ = e 15 := congrArg e h
           _ = _ := h15
    have hb : (e.symm j.val).val < 15 := by
      have hlt := (e.symm j.val).isLt
      have hv : (e.symm j.val).val ≠ 15 := by
        intro h; exact hne (Fin.ext h)
      omega
    refine ⟨⟨(e.symm j.val).val,hb⟩, ?_⟩
    apply Subtype.ext
    change e (⟨(e.symm j.val).val, _⟩ : Fin 16) = j.val
    exact e.apply_symm_apply j.val

@[simp] theorem omissionEquiv_apply (t : Bool) (i j : Fin 15) :
    (omissionEquiv t i j).val = orient t i j.castSucc := rfl

theorem omissionEquiv_mark (t : Bool) (i : Fin 15) :
    omissionEquiv t i i = markPosition (markRepresentative t i) := by
  apply Subtype.ext
  exact orient_mark t i

structure OmittedNeighborhoodMap (c : Host) (root : Fin 60) (q : FourColor)
    (t : Bool) (omitted : Fin 15) where
  vertex : Surviving omitted ↪ Fin 60
  mem_neighborhood : ∀ j, vertex j ∈ colorNeighborhood c q root
  covers_neighborhood : ∀ v ∈ colorNeighborhood c q root, ∃ j, vertex j = v
  colors : Fin 3 ≃ {a : FourColor // a ≠ q}
  map_color : ∀ a b, a ≠ b → c (vertex a) (vertex b) =
    (colors (R4333.k16Template t a.val b.val)).val

/-- The marked15-cell is expressed on exactly the surviving reference positions
used by the E formulas. The template type and its physical palette stay fixed. -/
theorem physical_marked_omission {c : Host} {root : Fin 60} {q : FourColor} {t : Bool}
    (m : PhysicalNeighborhoodMap c root q (R4333.k15Template t))
    (mark : Fin 60) (hmark : mark ∈ colorNeighborhood c q root) :
    ∃ omitted ∈ markRepresentatives t,
      ∃ n : OmittedNeighborhoodMap c root q t omitted,
        n.colors = m.colors ∧ n.vertex (markPosition omitted) = mark := by
  obtain ⟨i, hi⟩ := m.covers_neighborhood mark hmark
  let e := omissionEquiv t i
  let f : Surviving (markRepresentative t i) ↪ Fin 60 :=
    e.symm.toEmbedding.trans m.vertex
  have hc : ∀ a b, a ≠ b → c (f a) (f b) =
      (m.colors (R4333.k16Template t a.val b.val)).val := by
    intro a b hab
    change c (m.vertex (e.symm a)) (m.vertex (e.symm b)) =
      (m.colors (R4333.k16Template t a.val b.val)).val
    rw [m.map_color (e.symm a) (e.symm b) (e.symm.injective.ne hab)]
    rw [k15Template_castSucc]
    have hp := orient_preserves t i (e.symm a).castSucc (e.symm b).castSucc
      (fun h => hab (e.symm.injective (Fin.ext (congrArg (fun x : Fin 16 => x.val) h))))
    have ha : orient t i (e.symm a).castSucc = a.val := by
      change (e (e.symm a)).val = a.val
      rw [e.apply_symm_apply]
    have hb : orient t i (e.symm b).castSucc = b.val := by
      change (e (e.symm b)).val = b.val
      rw [e.apply_symm_apply]
    rw [ha,hb] at hp
    rw [hp]
  let n : OmittedNeighborhoodMap c root q t (markRepresentative t i) := {
    vertex := f
    mem_neighborhood := fun j => m.mem_neighborhood (e.symm j)
    covers_neighborhood := by
      intro v hv
      obtain ⟨j,hj⟩ := m.covers_neighborhood v hv
      refine ⟨e j, ?_⟩
      simpa [f] using hj
    colors := m.colors
    map_color := hc }
  refine ⟨markRepresentative t i, markRepresentative_mem t i, n, rfl, ?_⟩
  change m.vertex (e.symm (markPosition (markRepresentative t i))) = mark
  rw [← omissionEquiv_mark t i, e.symm_apply_apply, hi]

#print axioms physical_marked_omission
end UniformK60.ClassificationMarkedOmission
