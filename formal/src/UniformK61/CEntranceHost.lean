import UniformK61.CEntranceRepresentative

set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Finset


theorem freeSize_le_five (five : Bool) : freeSize five ≤ 5 := by cases five <;> decide

variable {c : Host} {five lt rt : Bool}

/-- The small root cell outside the entire retained marked support. -/
def omitted (b : Blocks c five lt rt) : Finset Vertex :=
  colorNeighborhood c (palette 0) b.entrance.root \ (univ.image b.free)

theorem free_image_subset (b : Blocks c five lt rt) :
    univ.image b.free ⊆ colorNeighborhood c (palette 0) b.entrance.root := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  exact b.free_mem i

theorem omitted_card (b : Blocks c five lt rt) : (omitted b).card = 14-freeSize five := by
  rw [omitted,card_sdiff_of_subset (free_image_subset b),card_image_of_injective _ b.free.injective]
  simpa [card_univ,Fintype.card_fin,colorDegree,rootSize] using congrArg (fun n => n-freeSize five) (b.entrance.degrees 0)

noncomputable def omittedEquiv (b : Blocks c five lt rt) :
    Fin (14-freeSize five) ≃ omitted b :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using omitted_card b)).symm

/-- Keep all retained coordinates and enumerate only the omitted vertices. -/
noncomputable def low (b : Blocks c five lt rt) (i : Fin (14)) : Vertex :=
  if h : i.val < freeSize five then b.free ⟨i.val,h⟩
  else (omittedEquiv b ⟨i.val-freeSize five,by have := freeSize_le_five five;omega⟩).val

theorem low_mem (b : Blocks c five lt rt) (i : Fin (14)) :
    low b i ∈ colorNeighborhood c (palette 0) b.entrance.root := by
  unfold low
  split_ifs with h
  · exact b.free_mem _
  · exact (mem_sdiff.mp (omittedEquiv b _).property).1

theorem low_initial (b : Blocks c five lt rt) (i : Fin (freeSize five)) :
    low b ⟨i.val,by have := freeSize_le_five five;omega⟩ = b.free i := by
  simp only [low,i.isLt,dif_pos]

theorem low_omitted (b : Blocks c five lt rt) (i : Fin (14))
    (hi : freeSize five ≤ i.val) : low b i ∈ omitted b := by
  simp only [low,show ¬ i.val < freeSize five by omega]
  exact (omittedEquiv b _).property

theorem low_injective (b : Blocks c five lt rt) : Function.Injective (low b) := by
  intro i j he
  by_cases hi : i.val < freeSize five <;> by_cases hj : j.val < freeSize five
  · simp only [low,hi,hj,dif_pos] at he
    exact Fin.ext (congrArg (fun x : Fin (freeSize five) => x.val) (b.free.injective he))
  · have hm := (mem_sdiff.mp (low_omitted b j (by omega))).2
    apply False.elim
    apply hm
    rw [←he]
    simp only [low,hi,dif_pos]
    exact mem_image.mpr ⟨⟨i.val,hi⟩,mem_univ _,rfl⟩
  · have hm := (mem_sdiff.mp (low_omitted b i (by omega))).2
    apply False.elim
    apply hm
    rw [he]
    simp only [low,hj,dif_pos]
    exact mem_image.mpr ⟨⟨j.val,hj⟩,mem_univ _,rfl⟩
  · simp only [low,hi,hj] at he
    have hh := (omittedEquiv b).injective (Subtype.ext he)
    have hh' := congrArg Fin.val hh
    apply Fin.ext
    simp only at hh'
    omega

/-- Exact support extraction, not an assumption that a partial coloring extends. -/
theorem omitted_not_marked (b : Blocks c five lt rt) (v : Vertex) (hv : v ∈ omitted b) :
    c (b.entrance.mark) v ≠ palette 3 := by
  intro he
  obtain ⟨hcell,hnot⟩ := mem_sdiff.mp hv
  have hne : v ≠ b.entrance.mark := by
    intro hh
    have h0 := (mem_colorNeighborhood _ _ _ _).mp hcell |>.2
    have h3 := (mem_colorNeighborhood _ _ _ _).mp (b.entrance.mark_mem) |>.2
    rw [hh] at h0
    have bad := palette_injective (h0.symm.trans h3)
    contradiction
  have hs : v ∈ attachingSupport c b.entrance.root (palette 3) (b.entrance.mark) (palette 0) :=
    mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨hne,he⟩,hcell⟩
  obtain ⟨i,hi⟩ := (b.free_exact v).mp hs
  exact hnot (mem_image.mpr ⟨i,mem_univ _,hi⟩)

/-- Enumerate the thirteen other actual vertices in the marked root cell. -/
def markedRest (e : Entrance c) : Finset Vertex :=
  (colorNeighborhood c (palette 3) e.root).erase e.mark

theorem markedRest_card (e : Entrance c) : (markedRest e).card = 13 := by
  rw [markedRest,card_erase_of_mem e.mark_mem]
  have h := e.degrees 3
  change (colorNeighborhood c (palette 3) e.root).card = 14 at h
  omega

noncomputable def markedRestEquiv (e : Entrance c) : Fin 13 ≃ markedRest e :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using markedRest_card e)).symm

noncomputable def marked (e : Entrance c) (i : Fin 14) : Vertex :=
  if h : i.val < 13 then (markedRestEquiv e ⟨i.val,h⟩).val else e.mark

theorem marked_mem (e : Entrance c) (i : Fin 14) :
    marked e i ∈ colorNeighborhood c (palette 3) e.root := by
  unfold marked
  split_ifs with h
  · exact (mem_erase.mp (markedRestEquiv e _).property).2
  · exact e.mark_mem

@[simp] theorem marked_last (e : Entrance c) : marked e 13 = e.mark := rfl

theorem marked_injective (e : Entrance c) : Function.Injective (marked e) := by
  intro i j he
  by_cases hi : i.val < 13 <;> by_cases hj : j.val < 13
  · simp only [marked,hi,hj,dif_pos] at he
    exact Fin.ext (congrArg (fun v : Fin 13 => v.val) ((markedRestEquiv e).injective (Subtype.ext he)))
  · simp only [marked,hi,hj,dif_pos,dif_neg] at he
    exact False.elim ((mem_erase.mp (markedRestEquiv e _).property).1 he)
  · simp only [marked,hi,hj,dif_pos,dif_neg] at he
    exact False.elim ((mem_erase.mp (markedRestEquiv e _).property).1 he.symm)
  · apply Fin.ext
    have hi' := i.isLt
    have hj' := j.isLt
    omega

abbrev FullParts := Unit ⊕ (Fin 14 ⊕ (Fin 16 ⊕ (Fin 16 ⊕ Fin 14)))

noncomputable def fullIndex : FullParts ≃ Vertex :=
  ((Equiv.sumCongr (Fintype.equivFinOfCardEq (show Fintype.card Unit=1 by decide))
    ((Equiv.sumCongr (Equiv.refl (Fin 14))
      ((Equiv.sumCongr (Equiv.refl (Fin 16)) finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by decide))

noncomputable def fullParts (b : Blocks c five lt rt) : FullParts → Vertex
  | .inl _ => b.entrance.root
  | .inr (.inl i) => low b i
  | .inr (.inr (.inl i)) => b.left.vertex i
  | .inr (.inr (.inr (.inl i))) => b.right.vertex i
  | .inr (.inr (.inr (.inr i))) => marked b.entrance i

def fullOwner : Fin 14 ⊕ (Fin 16 ⊕ (Fin 16 ⊕ Fin 14)) → Color
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

theorem fullParts_mem (b : Blocks c five lt rt) (i) :
    fullParts b (.inr i) ∈ colorNeighborhood c (palette (fullOwner i)) b.entrance.root := by
  rcases i with i|i|i|i
  · exact low_mem b i
  · exact b.left.mem_neighborhood i
  · exact b.right.mem_neighborhood i
  · exact marked_mem b.entrance i

theorem fullParts_injective (b : Blocks c five lt rt) : Function.Injective (fullParts b) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j => cases i;cases j;rfl
    | inr j => exact False.elim (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b j)).1 he.symm)
  | inr i =>
    cases j with
    | inl j => exact False.elim (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b i)).1 he)
    | inr j =>
      have ho : fullOwner i=fullOwner j := by
        apply palette_injective
        exact (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b i)).2.symm.trans
          (congrArg (c b.entrance.root) he)).trans (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b j)).2)
      rcases i with i|i|i|i <;> rcases j with j|j|j|j
      all_goals simp only [fullOwner] at ho
      all_goals try contradiction
      · exact congrArg (fun x => Sum.inr (Sum.inl x)) (low_injective b he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (b.left.vertex.injective he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))) (b.right.vertex.injective he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))) (marked_injective b.entrance he)

noncomputable def fullMap (b : Blocks c five lt rt) : Vertex ↪ Vertex :=
  fullIndex.symm.toEmbedding.trans ⟨fullParts b,fullParts_injective b⟩

/-- A complete relabeling of the single original sixty-one-vertex coloring. -/
noncomputable def coloring (b : Blocks c five lt rt) : Host where
  color u v := c (fullMap b u) (fullMap b v)
  color_symm _ _ := c.color_symm _ _

theorem coloring_good (b : Blocks c five lt rt) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (coloring b) := by
  intro u v w hd hm
  exact hc _ _ _ ⟨(fullMap b).injective.ne hd.1,(fullMap b).injective.ne hd.2.1,
    (fullMap b).injective.ne hd.2.2⟩ hm

def lowVertex (i : Fin 14) : Vertex := ⟨1+i.val,by omega⟩
def leftVertex (i : Fin 16) : Vertex := ⟨15+i.val,by omega⟩
def rightVertex (i : Fin 16) : Vertex := ⟨31+i.val,by omega⟩
def markedVertex (i : Fin 14) : Vertex := ⟨47+i.val,by omega⟩

theorem index_root : fullIndex (.inl ())=0 := by apply Fin.ext; simp [fullIndex,finSumFinEquiv]
theorem index_low (i : Fin 14) : fullIndex (.inr (.inl i))=lowVertex i := by
  apply Fin.ext; simp [fullIndex,lowVertex,finSumFinEquiv]
theorem index_left (i : Fin 16) : fullIndex (.inr (.inr (.inl i)))=leftVertex i := by
  apply Fin.ext; simp [fullIndex,leftVertex,finSumFinEquiv]; omega
theorem index_right (i : Fin 16) : fullIndex (.inr (.inr (.inr (.inl i))))=rightVertex i := by
  apply Fin.ext; simp [fullIndex,rightVertex,finSumFinEquiv]; omega
theorem index_marked (i : Fin 14) : fullIndex (.inr (.inr (.inr (.inr i))))=markedVertex i := by
  apply Fin.ext; simp [fullIndex,markedVertex,finSumFinEquiv]; omega

@[simp] theorem fullMap_root (b : Blocks c five lt rt) : fullMap b 0=b.entrance.root := by
  change fullParts b (fullIndex.symm 0)=_
  rw [←index_root,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_low (b : Blocks c five lt rt) (i : Fin 14) : fullMap b (lowVertex i)=low b i := by
  change fullParts b (fullIndex.symm _)=_
  rw [←index_low i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_left (b : Blocks c five lt rt) (i : Fin 16) : fullMap b (leftVertex i)=b.left.vertex i := by
  change fullParts b (fullIndex.symm _)=_
  rw [←index_left i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_right (b : Blocks c five lt rt) (i : Fin 16) : fullMap b (rightVertex i)=b.right.vertex i := by
  change fullParts b (fullIndex.symm _)=_
  rw [←index_right i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_marked (b : Blocks c five lt rt) (i : Fin 14) : fullMap b (markedVertex i)=marked b.entrance i := by
  change fullParts b (fullIndex.symm _)=_
  rw [←index_marked i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_mark (b : Blocks c five lt rt) : fullMap b 60=b.entrance.mark :=
  (fullMap_marked b 13).trans (marked_last b.entrance)

#print axioms fullParts_injective
#print axioms coloring_good
end UniformK61.CEntrance
