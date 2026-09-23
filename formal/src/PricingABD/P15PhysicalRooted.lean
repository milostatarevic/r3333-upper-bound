import PricingABD.Rooted455Free
import PricingABD.SupportTransport

namespace PricingABD.P15PhysicalRooted
open Ramsey61 Ramsey61.CEncodingCore PricingABD.TTExchange PricingABD.P15Encoder
open PricingABD.P15MatrixTransport PricingABD.Rooted455Entrance PricingABD.Rooted455Free
open PricingABD.Rooted455Data

/-- The exact canonical ordering of the first archived TT support representative. -/
def supportOrder : Fin 5 → Fin 15 := ![0,1,13,2,10]

def restoredVertex {c : Host} {t : Bool} (f : Frame c 4 t) (i : Fin 15) : Fin 61 :=
  if h : i.val < 14 then physicalVertex f (placement ⟨i.val,h⟩) else f.root

theorem restored_old {c : Host} {t : Bool} (f : Frame c 4 t) (i : Fin 14) :
    restoredVertex f i.castSucc=physicalVertex f (placement i) := by simp [restoredVertex]

theorem restored_root {c : Host} {t : Bool} (f : Frame c 4 t) : restoredVertex f 14=f.root := rfl

theorem restored_zero {c : Host} {t : Bool} (f : Frame c 4 t) (i : Fin 4) :
    restoredVertex f (label0 i)=f.free i := by
  have hi : i.val < 14 := by omega
  rw [show label0 i=(⟨i.val,hi⟩ : Fin 14).castSucc from rfl,restored_old]
  have hm : placement ⟨i.val,hi⟩=freeVertex i := by fin_cases i <;> rfl
  rw [hm,physicalVertex_free]

theorem restored_one {c : Host} {t : Bool} (f : Frame c 4 t) (i : Fin 5) :
    restoredVertex f (label1 i)=f.left (supportOrder i) := by
  have hi : 4+i.val < 14 := by omega
  rw [show label1 i=(⟨4+i.val,hi⟩ : Fin 14).castSucc from rfl,restored_old]
  have hm : placement ⟨4+i.val,hi⟩=leftVertex (supportOrder i) := by fin_cases i <;> rfl
  rw [hm,physicalVertex_left]

theorem restored_two {c : Host} {t : Bool} (f : Frame c 4 t) (i : Fin 5) :
    restoredVertex f (label2 i)=f.right (supportOrder i) := by
  have hi : 9+i.val < 14 := by omega
  rw [show label2 i=(⟨9+i.val,hi⟩ : Fin 14).castSucc from rfl,restored_old]
  have hm : placement ⟨9+i.val,hi⟩=rightVertex (supportOrder i) := by fin_cases i <;> rfl
  rw [hm,physicalVertex_right]

theorem physical_ne_root {c : Host} {t : Bool} (f : Frame c 4 t) (i : Fin 50) :
    physicalVertex f i≠f.root := by
  change physical f (indexEquiv.symm i)≠f.root
  generalize indexEquiv.symm i=a
  rcases a with a | a | a | a
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.free_mem a)).1
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.left_mem a)).1
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.right_mem a)).1
  · exact ((mem_colorNeighborhood _ _ _ _).mp (f.marked_mem a)).1

theorem restored_injective {c : Host} {t : Bool} (f : Frame c 4 t) :
    Function.Injective (restoredVertex f) := by
  intro i j he
  by_cases hi : i.val < 14
  · by_cases hj : j.val < 14
    · simp only [restoredVertex,hi,hj,↓reduceDIte] at he
      have hh := placement.injective ((physicalVertex_injective f) he)
      apply Fin.ext;exact congrArg (fun x : Fin 14 => x.val) hh
    · simp only [restoredVertex,hi,hj,↓reduceDIte] at he
      exact False.elim (physical_ne_root f _ he)
  · by_cases hj : j.val < 14
    · simp only [restoredVertex,hi,hj,↓reduceDIte] at he
      exact False.elim (physical_ne_root f _ he.symm)
    · apply Fin.ext;omega

/-- These are actual incidences to one marked physical vertex, not an abstract
matrix/census premise. The mark and root are retained throughout the reduction. -/
structure Pair000Incidences {c : Host} {t : Bool} (f : Frame c 4 t) : Prop where
  free : ∀ i,c (f.marked 15) (f.free i)=palette 3
  left : ∀ i,c (f.marked 15) (f.left (supportOrder i))=palette 3
  right : ∀ i,c (f.marked 15) (f.right (supportOrder i))=palette 3

theorem restored_spoke {c : Host} {t : Bool} (f : Frame c 4 t) (h : Pair000Incidences f)
    (i : Fin 15) : c (f.marked 15) (restoredVertex f i)=palette 3 := by
  by_cases hi : i=14
  · subst i;rw [restored_root,c.color_symm];exact ((mem_colorNeighborhood _ _ _ _).mp (f.marked_mem 15)).2
  · by_cases h0 : i.val < 4
    · have he : i=label0 ⟨i.val,h0⟩ := rfl
      rw [he,restored_zero];exact h.free _
    · by_cases h1 : i.val < 9
      · have he : i=label1 ⟨i.val-4,by have:=i.isLt;omega⟩ := by apply Fin.ext;dsimp [label1];omega
        rw [he,restored_one];exact h.left _
      · have he : i=label2 ⟨i.val-9,by have:=i.isLt;have hv : i.val≠14 := fun hh => hi (Fin.ext hh);omega⟩ := by apply Fin.ext;dsimp [label2];omega
        rw [he,restored_two];exact h.right _

theorem mark_ne_restored {c : Host} {t : Bool} (f : Frame c 4 t) (i : Fin 15) :
    f.marked 15≠restoredVertex f i := by
  by_cases hi : i=14
  · subst i;exact ((mem_colorNeighborhood _ _ _ _).mp (f.marked_mem 15)).1
  · by_cases h0 : i.val < 4
    · have he : i=label0 ⟨i.val,h0⟩ := rfl
      rw [he,restored_zero];exact SupportTransport.distinct_root_cells (f.marked_mem 15) (f.free_mem _) (by decide)
    · by_cases h1 : i.val < 9
      · have he : i=label1 ⟨i.val-4,by omega⟩ := by apply Fin.ext;dsimp [label1];omega
        rw [he,restored_one];exact SupportTransport.distinct_root_cells (f.marked_mem 15) (f.left_mem _) (by decide)
      · have he : i=label2 ⟨i.val-9,by have hv : i.val≠14 := fun hh => hi (Fin.ext hh);omega⟩ := by apply Fin.ext;dsimp [label2];omega
        rw [he,restored_two];exact SupportTransport.distinct_root_cells (f.marked_mem 15) (f.right_mem _) (by decide)

theorem restored_avoids_three {c : Host} {t : Bool} (f : Frame c 4 t) (h : Pair000Incidences f)
    (hc : NoMonochromaticTriangle c) (i j : Fin 15) (hij : i≠j) :
    c (restoredVertex f i) (restoredVertex f j)≠palette 3 := by
  intro hh
  exact hc (f.marked 15) (restoredVertex f i) (restoredVertex f j)
    ⟨mark_ne_restored f i,mark_ne_restored f j,(restored_injective f).ne hij⟩
    ⟨(restored_spoke f h i).trans (restored_spoke f h j).symm,(restored_spoke f h j).trans hh.symm⟩

def threeIndex : FourColor → Fin 3
  | (false,false) => 0
  | (false,true) => 1
  | (true,false) => 2
  | (true,true) => 0

theorem threeIndex_palette (q : Fin 3) : threeIndex (palette (Fin.castLE (by decide) q))=q := by fin_cases q <;> rfl

theorem palette_threeIndex (q : FourColor) (h : q≠palette 3) : palette (Fin.castLE (by decide) (threeIndex q))=q := by
  rcases q with ⟨a,b⟩;cases a <;> cases b <;> simp_all [threeIndex,palette]

theorem threeIndex_injective_on {a b : FourColor} (ha : a≠palette 3) (hb : b≠palette 3)
    (h : threeIndex a=threeIndex b) : a=b := by
  rw [←palette_threeIndex a ha,←palette_threeIndex b hb,h]

def restoredColoring {c : Host} {t : Bool} (f : Frame c 4 t) : R4333.EdgeColoring (Fin 15) (Fin 3) where
  color i j := threeIndex (c (restoredVertex f i) (restoredVertex f j))
  color_symm i j := congrArg threeIndex (c.color_symm _ _)

theorem restored_good {c : Host} {t : Bool} (f : Frame c 4 t) (h : Pair000Incidences f)
    (hc : NoMonochromaticTriangle c) : R4333.NoMonochromaticTriangle (restoredColoring f) := by
  intro a b d hd hm
  apply hc (restoredVertex f a) (restoredVertex f b) (restoredVertex f d)
    ⟨(restored_injective f).ne hd.1,(restored_injective f).ne hd.2.1,(restored_injective f).ne hd.2.2⟩
  exact ⟨threeIndex_injective_on (restored_avoids_three f h hc a b hd.1) (restored_avoids_three f h hc a d hd.2.1) hm.1,
    threeIndex_injective_on (restored_avoids_three f h hc a d hd.2.1) (restored_avoids_three f h hc b d hd.2.2) hm.2⟩

#print axioms restored_good
end PricingABD.P15PhysicalRooted
