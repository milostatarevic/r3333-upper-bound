import CompletionC.CommonBlocks

set_option autoImplicit false
namespace UniformK61.CommonHost
open Ramsey61 Ramsey61.CEncodingCore Finset
open PricingABD PricingABD.ABLayout CompletionC.CommonBlocks

variable {c : Host} {l : Layout} {t : Types}

/-- The small root cell outside the entire retained marked support. -/
def omitted (b : Blocks c l t) : Finset Vertex :=
  colorNeighborhood c (palette 0) b.root \ (univ.image b.free)

theorem free_image_subset (b : Blocks c l t) :
    univ.image b.free ⊆ colorNeighborhood c (palette 0) b.root := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  exact b.free_mem i

theorem omitted_card (b : Blocks c l t) : (omitted b).card = lowSize l-freeSize l := by
  rw [omitted,card_sdiff_of_subset (free_image_subset b),card_image_of_injective _ b.free.injective]
  simpa only [card_univ,Fintype.card_fin,colorDegree] using congrArg (fun n => n-freeSize l) b.low_degree

noncomputable def omittedEquiv (b : Blocks c l t) :
    Fin (lowSize l-freeSize l) ≃ omitted b :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using omitted_card b)).symm

/-- Keep all retained coordinates and enumerate only the omitted vertices. -/
noncomputable def low (b : Blocks c l t) (i : Fin (lowSize l)) : Vertex :=
  if h : i.val < freeSize l then b.free ⟨i.val,h⟩
  else (omittedEquiv b ⟨i.val-freeSize l,by have := sizes l;omega⟩).val

theorem low_mem (b : Blocks c l t) (i : Fin (lowSize l)) :
    low b i ∈ colorNeighborhood c (palette 0) b.root := by
  unfold low
  split_ifs with h
  · exact b.free_mem _
  · exact (mem_sdiff.mp (omittedEquiv b _).property).1

theorem low_initial (b : Blocks c l t) (i : Fin (freeSize l)) :
    low b ⟨i.val,by have := sizes l;omega⟩ = b.free i := by
  simp only [low,i.isLt,dif_pos]

theorem low_omitted (b : Blocks c l t) (i : Fin (lowSize l))
    (hi : freeSize l ≤ i.val) : low b i ∈ omitted b := by
  simp only [low,show ¬ i.val < freeSize l by omega]
  exact (omittedEquiv b _).property

theorem low_injective (b : Blocks c l t) : Function.Injective (low b) := by
  intro i j he
  by_cases hi : i.val < freeSize l <;> by_cases hj : j.val < freeSize l
  · simp only [low,hi,hj,dif_pos] at he
    exact Fin.ext (congrArg (fun x : Fin (freeSize l) => x.val) (b.free.injective he))
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
theorem omitted_not_marked (b : Blocks c l t) (v : Vertex) (hv : v ∈ omitted b) :
    c (b.marked.vertex 15) v ≠ palette 3 := by
  intro he
  obtain ⟨hcell,hnot⟩ := mem_sdiff.mp hv
  have hne : v ≠ b.marked.vertex 15 := by
    intro hh
    have h0 := (mem_colorNeighborhood _ _ _ _).mp hcell |>.2
    have h3 := (mem_colorNeighborhood _ _ _ _).mp (b.marked.mem_neighborhood 15) |>.2
    rw [hh] at h0
    have bad := palette_injective (h0.symm.trans h3)
    contradiction
  have hs : v ∈ attachingSupport c b.root (palette 3) (b.marked.vertex 15) (palette 0) :=
    mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨hne,he⟩,hcell⟩
  obtain ⟨i,hi⟩ := (b.free_exact v).mp hs
  exact hnot (mem_image.mpr ⟨i,mem_univ _,hi⟩)

abbrev FullParts (l : Layout) := Unit ⊕
  (Fin (lowSize l) ⊕ (Fin (leftSize l) ⊕ (Fin (rightSize l) ⊕ Fin 16)))

noncomputable def fullIndex (l : Layout) : FullParts l ≃ Fin 61 :=
  ((Equiv.sumCongr (Fintype.equivFinOfCardEq (show Fintype.card Unit=1 by decide))
    ((Equiv.sumCongr (Equiv.refl (Fin (lowSize l)))
      ((Equiv.sumCongr (Equiv.refl (Fin (leftSize l))) finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by have := sizes l;unfold lowSize tailSize;omega))

noncomputable def fullParts (b : Blocks c l t) : FullParts l → Vertex
  | .inl _ => b.root
  | .inr (.inl i) => low b i
  | .inr (.inr (.inl i)) => b.left.vertex i
  | .inr (.inr (.inr (.inl i))) => b.right.vertex i
  | .inr (.inr (.inr (.inr i))) => b.marked.vertex i

def fullOwner {l : Layout} : Fin (lowSize l) ⊕
    (Fin (leftSize l) ⊕ (Fin (rightSize l) ⊕ Fin 16)) → Fin 4
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

theorem fullParts_mem (b : Blocks c l t) (i) :
    fullParts b (.inr i) ∈ colorNeighborhood c (palette (fullOwner i)) b.root := by
  rcases i with i|i|i|i
  · exact low_mem b i
  · exact b.left.mem_neighborhood i
  · exact b.right.mem_neighborhood i
  · exact b.marked.mem_neighborhood i

theorem fullParts_injective (b : Blocks c l t) : Function.Injective (fullParts b) := by
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
          (congrArg (c b.root) he)).trans (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b j)).2)
      rcases i with i|i|i|i <;> rcases j with j|j|j|j
      all_goals simp only [fullOwner] at ho
      all_goals try contradiction
      · exact congrArg (fun x => Sum.inr (Sum.inl x)) (low_injective b he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (b.left.vertex.injective he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))) (b.right.vertex.injective he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))) (b.marked.vertex.injective he)

noncomputable def fullMap (b : Blocks c l t) : Vertex ↪ Vertex :=
  (fullIndex l).symm.toEmbedding.trans ⟨fullParts b,fullParts_injective b⟩

/-- All coordinates come from one actual host. -/
noncomputable def coloring (b : Blocks c l t) : Host where
  color u v := c (fullMap b u) (fullMap b v)
  color_symm _ _ := c.color_symm _ _

theorem coloring_good (b : Blocks c l t) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (coloring b) := by
  intro u v w hd hm
  exact hc _ _ _ ⟨(fullMap b).injective.ne hd.1,(fullMap b).injective.ne hd.2.1,
    (fullMap b).injective.ne hd.2.2⟩ hm

def lowVertex (l : Layout) (i : Fin (lowSize l)) : Vertex :=
  ⟨1+i.val,by have := sizes l;omega⟩
def leftVertex (l : Layout) (i : Fin (leftSize l)) : Vertex :=
  ⟨1+lowSize l+i.val,by have := sizes l;unfold lowSize tailSize;omega⟩
def rightVertex (l : Layout) (i : Fin (rightSize l)) : Vertex :=
  ⟨1+lowSize l+leftSize l+i.val,by have := sizes l;unfold lowSize tailSize;omega⟩
def markedVertex (_l : Layout) (i : Fin 16) : Vertex :=
  ⟨45+i.val,by omega⟩

theorem index_root (l : Layout) : fullIndex l (.inl ())=0 := by
  apply Fin.ext
  simp [fullIndex,finSumFinEquiv]

theorem index_low (l : Layout) (i : Fin (lowSize l)) :
    fullIndex l (.inr (.inl i))=lowVertex l i := by
  apply Fin.ext
  simp [fullIndex,lowVertex,finSumFinEquiv]
theorem index_left (l : Layout) (i : Fin (leftSize l)) :
    fullIndex l (.inr (.inr (.inl i)))=leftVertex l i := by
  apply Fin.ext
  simp [fullIndex,leftVertex,finSumFinEquiv,Nat.add_assoc]
theorem index_right (l : Layout) (i : Fin (rightSize l)) :
    fullIndex l (.inr (.inr (.inr (.inl i))))=rightVertex l i := by
  apply Fin.ext
  simp [fullIndex,rightVertex,finSumFinEquiv,Nat.add_assoc]
theorem index_marked (l : Layout) (i : Fin 16) :
    fullIndex l (.inr (.inr (.inr (.inr i))))=markedVertex l i := by
  apply Fin.ext
  change 1+(lowSize l+(leftSize l+(rightSize l+i.val)))=45+i.val
  have := sizes l
  simp only [lowSize,tailSize]
  omega

@[simp] theorem fullMap_root (b : Blocks c l t) : fullMap b 0=b.root := by
  change fullParts b ((fullIndex l).symm 0)=_
  rw [←index_root l,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_low (b : Blocks c l t) (i : Fin (lowSize l)) :
    fullMap b (lowVertex l i)=low b i := by
  change fullParts b ((fullIndex l).symm _)=_
  rw [←index_low l i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_left (b : Blocks c l t) (i : Fin (leftSize l)) :
    fullMap b (leftVertex l i)=b.left.vertex i := by
  change fullParts b ((fullIndex l).symm _)=_
  rw [←index_left l i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_right (b : Blocks c l t) (i : Fin (rightSize l)) :
    fullMap b (rightVertex l i)=b.right.vertex i := by
  change fullParts b ((fullIndex l).symm _)=_
  rw [←index_right l i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_marked (b : Blocks c l t) (i : Fin 16) :
    fullMap b (markedVertex l i)=b.marked.vertex i := by
  change fullParts b ((fullIndex l).symm _)=_
  rw [←index_marked l i,Equiv.symm_apply_apply];rfl
@[simp] theorem fullMap_mark (b : Blocks c l t) : fullMap b 60=b.marked.vertex 15 :=
  fullMap_marked b 15

def retainNat (l : Layout) (i : Nat) : Nat :=
  if i < freeSize l then 1+i else 1+lowSize l+(i-freeSize l)
def retain (l : Layout) (i : Fin (vertexCount l)) : Vertex :=
  ⟨retainNat l i.val,by
    have := sizes l
    unfold retainNat
    split_ifs <;> unfold vertexCount lowSize tailSize at * <;> omega⟩

theorem retain_free (l : Layout) (i : Fin (freeSize l)) :
    retain l (ABLayout.free l i)=lowVertex l ⟨i.val,by have := sizes l;omega⟩ := by
  apply Fin.ext;simp [retain,retainNat,ABLayout.free,lowVertex,i.isLt]
theorem retain_left (l : Layout) (i : Fin (leftSize l)) :
    retain l (ABLayout.left l i)=leftVertex l i := by
  apply Fin.ext;simp [retain,retainNat,ABLayout.left,ABLayout.leftStart,leftVertex]
theorem retain_right (l : Layout) (i : Fin (rightSize l)) :
    retain l (ABLayout.right l i)=rightVertex l i := by
  apply Fin.ext
  simp only [retain,retainNat,ABLayout.right,ABLayout.rightStart,rightVertex]
  split_ifs <;> omega
theorem retain_marked (l : Layout) (i : Fin 16) :
    retain l (ABLayout.marked l i)=markedVertex l i := by
  apply Fin.ext
  have := sizes l
  simp only [retain,retainNat,ABLayout.marked,ABLayout.markedStart,markedVertex]
  split_ifs <;> simp only [lowSize,tailSize] at * <;> omega

@[simp] theorem fullMap_retain (b : Blocks c l t) (i : Fin (vertexCount l)) :
    fullMap b (retain l i)=physical b i := by
  obtain ⟨j,rfl⟩ := (CompletionC.CommonBlocks.indexEquiv l).surjective i
  rcases j with j|j|j|j
  · rw [CompletionC.CommonBlocks.index_free,retain_free,fullMap_low,low_initial,physical_free]
  · rw [CompletionC.CommonBlocks.index_left,retain_left,fullMap_left,physical_left]
  · rw [CompletionC.CommonBlocks.index_right,retain_right,fullMap_right,physical_right]
  · rw [CompletionC.CommonBlocks.index_marked,retain_marked,fullMap_marked,physical_marked]

theorem retain_injective (l : Layout) : Function.Injective (retain l) := by
  intro i j he
  have hv := congrArg Fin.val he
  dsimp [retain,retainNat] at hv
  apply Fin.ext
  split_ifs at hv <;> have := sizes l <;> omega

end UniformK61.CommonHost
