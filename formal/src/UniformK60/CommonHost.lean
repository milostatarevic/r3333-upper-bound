import UniformK60.CommonBlocks
import UniformK60.HostNormalizationExtension
import UniformK60.ClassificationMarkedOmission
import UniformK60.UnitRestriction

/-! Complete physical K60 placements for the common and U/U marked cases.
`none` omits the last free reference vertex; `some r` omits marked reference
position r. The marked template supplies only actual surviving vertices. -/
set_option autoImplicit false
namespace UniformK60.CommonHost
open Ramsey61 Finset UniformK60.Physical UniformK60.HostNormalization
open UniformK60.ClassificationAdapter UniformK60.ClassificationMarkedOmission
open UniformK60.ClassificationGeometry UniformK60.PhysicalHelpers
open PricingABD.ABLayout UniformK60.CommonBlocks

abbrev Missing := Option (Fin 15)

abbrev markedSize : Missing → Nat | none => 16 | some _ => 15

def actualLow (l : Layout) : Missing → Nat
  | none => lowSize l-1
  | some _ => lowSize l

def omission (l : Layout) : Missing → UnitRestriction.Omission
  | none => ⟨lowSize l,by have := sizes l;omega⟩
  | some r => ⟨45+r.val,by omega⟩

def markedPosition : (missing : Missing) → Fin (markedSize missing) → Fin 16
  | none,i => i
  | some r,i => r.castSucc.succAbove i

def markIndex : (missing : Missing) → Fin (markedSize missing)
  | none => ⟨15,by change 15<16;decide⟩
  | some _ => ⟨14,by change 14<15;decide⟩

@[simp] theorem markedPosition_mark (missing : Missing) :
    markedPosition missing (markIndex missing)=15 := by
  cases missing with
  | none => rfl
  | some r =>
    change r.castSucc.succAbove (14 : Fin 15)=15
    rw [Fin.succAbove_of_le_castSucc _ _ (by change r.val≤14;omega)]
    rfl

theorem markedPosition_injective (missing : Missing) :
    Function.Injective (markedPosition missing) := by
  cases missing
  · exact Function.injective_id
  · exact Fin.succAbove_right_injective

/-- The complete actual marked cell in a full or punctured16-template. -/
structure MarkedBlock (c : Host) (r : Vertex) (t : Bool) (missing : Missing) where
  vertex : Fin (markedSize missing) ↪ Vertex
  mem_neighborhood : ∀ i,vertex i ∈ colorNeighborhood c (palette 3) r
  map_color : ∀ i j,i≠j → c (vertex i) (vertex j)=
    palette (UniformK60.PhysicalHelpers.foreign 3
      (R4333.k16Template t (markedPosition missing i) (markedPosition missing j)))

def ofFull {c : Host} {r : Vertex} {t : Bool}
    (m : PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template t))
    (hp : m.colors=foreignEquiv 3) : MarkedBlock c r t none where
  vertex := m.vertex
  mem_neighborhood := m.mem_neighborhood
  map_color i j hij := by rw [m.map_color i j hij,hp];rfl

def survivingIndex (r : Fin 15) : Fin 15 ↪ Surviving r where
  toFun i := ⟨r.castSucc.succAbove i,Fin.succAbove_ne _ _⟩
  inj' := fun _ _ h => Fin.succAbove_right_injective (congrArg Subtype.val h)

def ofOmitted {c : Host} {r : Vertex} {t : Bool} {missing : Fin 15}
    (m : OmittedNeighborhoodMap c r (palette 3) t missing)
    (hp : m.colors=foreignEquiv 3) : MarkedBlock c r t (some missing) where
  vertex := (survivingIndex missing).trans m.vertex
  mem_neighborhood i := m.mem_neighborhood _
  map_color i j hij := by
    change c (m.vertex (survivingIndex missing i)) (m.vertex (survivingIndex missing j))=_
    rw [m.map_color _ _ ((survivingIndex missing).injective.ne hij),hp]
    rfl

variable {c : Host} {l : Layout} {t : Types} {missing : Missing}

structure Completion (b : Blocks c l t) (missing : Missing) where
  marked : MarkedBlock c b.root t.marked missing
  mark_eq : marked.vertex (markIndex missing)=b.mark
  low_degree : colorDegree c (palette 0) b.root=actualLow l missing

theorem free_le_low (l : Layout) (missing : Missing) : freeSize l≤actualLow l missing := by
  have := sizes l
  cases missing <;> simp only [actualLow] <;> omega

theorem neighbor_sum (l : Layout) (missing : Missing) :
    actualLow l missing+leftSize l+rightSize l+markedSize missing=59 := by
  have := sizes l
  cases missing <;> simp only [actualLow,markedSize,lowSize,tailSize] at * <;> omega

noncomputable def lowMap (b : Blocks c l t) (h : Completion b missing) :
    Fin (actualLow l missing) ↪ Vertex :=
  Classical.choose (extend_cell_embedding c b.root (palette 0) (free_le_low l missing)
    h.low_degree b.free b.free_mem)

theorem low_initial (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (freeSize l)) : lowMap b h (Fin.castLE (free_le_low l missing) i)=b.free i :=
  (Classical.choose_spec (extend_cell_embedding c b.root (palette 0) (free_le_low l missing)
    h.low_degree b.free b.free_mem)).1 i

theorem low_mem (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (actualLow l missing)) : lowMap b h i ∈ colorNeighborhood c (palette 0) b.root :=
  (Classical.choose_spec (extend_cell_embedding c b.root (palette 0) (free_le_low l missing)
    h.low_degree b.free b.free_mem)).2.1 i

/-- Every unselected low position has negative marked-neighborhood membership. -/
theorem low_membership (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (actualLow l missing)) :
    c b.mark (lowMap b h i)=palette 3 ↔ i.val<freeSize l := by
  constructor
  · intro he
    have hne : lowMap b h i≠b.mark := by
      intro eq
      have h0 := ((mem_colorNeighborhood _ _ _ _).mp (low_mem b h i)).2
      have h3 := ((mem_colorNeighborhood _ _ _ _).mp b.mark_mem).2
      rw [eq] at h0
      exact (show (0 : Color)≠3 by decide) (palette_injective (h0.symm.trans h3))
    have hs : lowMap b h i ∈ attachingSupport c b.root (palette 3) b.mark (palette 0) :=
      mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨hne,he⟩,low_mem b h i⟩
    obtain ⟨j,hj⟩ := (b.free_exact _).mp hs
    have hij := (lowMap b h).injective ((low_initial b h j).trans hj)
    have hv : j.val=i.val := congrArg Fin.val hij
    have := j.isLt
    omega
  · intro hi
    let j : Fin (freeSize l) := ⟨i.val,hi⟩
    have he : Fin.castLE (free_le_low l missing) j=i := Fin.ext rfl
    rw [← he,low_initial]
    exact b.free_own j

abbrev FullParts (l : Layout) (missing : Missing) := Unit ⊕
  (Fin (actualLow l missing) ⊕
    (Fin (leftSize l) ⊕ (Fin (rightSize l) ⊕ Fin (markedSize missing))))

noncomputable def fullIndex (l : Layout) (missing : Missing) : FullParts l missing ≃ Vertex :=
  ((Equiv.sumCongr (Fintype.equivFinOfCardEq (show Fintype.card Unit=1 by decide))
    ((Equiv.sumCongr (Equiv.refl (Fin (actualLow l missing)))
      ((Equiv.sumCongr (Equiv.refl (Fin (leftSize l))) finSumFinEquiv).trans
        finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv).trans
    (finCongr (by have := neighbor_sum l missing;omega))

noncomputable def fullParts (b : Blocks c l t) (h : Completion b missing) :
    FullParts l missing → Vertex
  | .inl _ => b.root
  | .inr (.inl i) => lowMap b h i
  | .inr (.inr (.inl i)) => b.left.vertex i
  | .inr (.inr (.inr (.inl i))) => b.right.vertex i
  | .inr (.inr (.inr (.inr i))) => h.marked.vertex i

def fullOwner : Fin (actualLow l missing) ⊕
    (Fin (leftSize l) ⊕ (Fin (rightSize l) ⊕ Fin (markedSize missing))) → Color
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

theorem fullParts_mem (b : Blocks c l t) (h : Completion b missing) (i) :
    fullParts b h (.inr i) ∈ colorNeighborhood c (palette (fullOwner i)) b.root := by
  rcases i with i|i|i|i
  · exact low_mem b h i
  · exact b.left.mem_neighborhood i
  · exact b.right.mem_neighborhood i
  · exact h.marked.mem_neighborhood i

theorem fullParts_injective (b : Blocks c l t) (h : Completion b missing) :
    Function.Injective (fullParts b h) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j => cases i;cases j;rfl
    | inr j => exact False.elim (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b h j)).1 he.symm)
  | inr i =>
    cases j with
    | inl j => exact False.elim (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b h i)).1 he)
    | inr j =>
      have ho : fullOwner i=fullOwner j := by
        apply palette_injective
        exact (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b h i)).2.symm.trans
          (congrArg (c b.root) he)).trans (((mem_colorNeighborhood _ _ _ _).mp (fullParts_mem b h j)).2)
      rcases i with i|i|i|i <;> rcases j with j|j|j|j
      all_goals simp only [fullOwner] at ho
      all_goals try contradiction
      · exact congrArg (fun x => Sum.inr (Sum.inl x)) ((lowMap b h).injective he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (b.left.vertex.injective he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))) (b.right.vertex.injective he)
      · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))) (h.marked.vertex.injective he)

noncomputable def fullMap (b : Blocks c l t) (h : Completion b missing) : Vertex ↪ Vertex :=
  (fullIndex l missing).symm.toEmbedding.trans ⟨fullParts b h,fullParts_injective b h⟩

noncomputable def coloring (b : Blocks c l t) (h : Completion b missing) : Host where
  color u v := c (fullMap b h u) (fullMap b h v)
  color_symm _ _ := c.color_symm _ _

theorem coloring_good (b : Blocks c l t) (h : Completion b missing)
    (hc : NoMonochromaticTriangle c) : NoMonochromaticTriangle (coloring b h) := by
  intro u v w hd hm
  exact hc _ _ _ ⟨(fullMap b h).injective.ne hd.1,(fullMap b h).injective.ne hd.2.1,
    (fullMap b h).injective.ne hd.2.2⟩ hm

def lowVertex (l : Layout) (missing : Missing) (i : Fin (actualLow l missing)) : Vertex :=
  ⟨1+i.val,by have := neighbor_sum l missing;omega⟩
def leftVertex (l : Layout) (missing : Missing) (i : Fin (leftSize l)) : Vertex :=
  ⟨1+actualLow l missing+i.val,by have := neighbor_sum l missing;omega⟩
def rightVertex (l : Layout) (missing : Missing) (i : Fin (rightSize l)) : Vertex :=
  ⟨1+actualLow l missing+leftSize l+i.val,by have := neighbor_sum l missing;omega⟩
def markedVertex (l : Layout) (missing : Missing) (i : Fin (markedSize missing)) : Vertex :=
  ⟨1+actualLow l missing+leftSize l+rightSize l+i.val,
    by have := neighbor_sum l missing;omega⟩

theorem index_root (l : Layout) (missing : Missing) : fullIndex l missing (.inl ())=0 := by
  apply Fin.ext
  simp [fullIndex,finSumFinEquiv]

theorem index_low (l : Layout) (missing : Missing) (i : Fin (actualLow l missing)) :
    fullIndex l missing (.inr (.inl i))=lowVertex l missing i := by
  apply Fin.ext
  simp [fullIndex,lowVertex,finSumFinEquiv]

theorem index_left (l : Layout) (missing : Missing) (i : Fin (leftSize l)) :
    fullIndex l missing (.inr (.inr (.inl i)))=leftVertex l missing i := by
  apply Fin.ext
  simp [fullIndex,leftVertex,finSumFinEquiv,Nat.add_assoc]

theorem index_right (l : Layout) (missing : Missing) (i : Fin (rightSize l)) :
    fullIndex l missing (.inr (.inr (.inr (.inl i))))=rightVertex l missing i := by
  apply Fin.ext
  simp [fullIndex,rightVertex,finSumFinEquiv,Nat.add_assoc]

theorem index_marked (l : Layout) (missing : Missing) (i : Fin (markedSize missing)) :
    fullIndex l missing (.inr (.inr (.inr (.inr i))))=markedVertex l missing i := by
  apply Fin.ext
  simp [fullIndex,markedVertex,finSumFinEquiv,Nat.add_assoc]

@[simp] theorem fullMap_root (b : Blocks c l t) (h : Completion b missing) :
    fullMap b h 0=b.root := by
  change fullParts b h ((fullIndex l missing).symm 0)=_
  rw [←index_root l missing,Equiv.symm_apply_apply]
  rfl

@[simp] theorem fullMap_low (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (actualLow l missing)) : fullMap b h (lowVertex l missing i)=lowMap b h i := by
  change fullParts b h ((fullIndex l missing).symm _)=_
  rw [←index_low l missing i,Equiv.symm_apply_apply]
  rfl

@[simp] theorem fullMap_left (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (leftSize l)) : fullMap b h (leftVertex l missing i)=b.left.vertex i := by
  change fullParts b h ((fullIndex l missing).symm _)=_
  rw [←index_left l missing i,Equiv.symm_apply_apply]
  rfl

@[simp] theorem fullMap_right (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (rightSize l)) : fullMap b h (rightVertex l missing i)=b.right.vertex i := by
  change fullParts b h ((fullIndex l missing).symm _)=_
  rw [←index_right l missing i,Equiv.symm_apply_apply]
  rfl

@[simp] theorem fullMap_marked (b : Blocks c l t) (h : Completion b missing)
    (i : Fin (markedSize missing)) :
    fullMap b h (markedVertex l missing i)=h.marked.vertex i := by
  change fullParts b h ((fullIndex l missing).symm _)=_
  rw [←index_marked l missing i,Equiv.symm_apply_apply]
  rfl

theorem markedVertex_mark (l : Layout) (missing : Missing) :
    markedVertex l missing (markIndex missing)=59 := by
  apply Fin.ext
  have := neighbor_sum l missing
  cases missing <;> simp only [markedVertex,markIndex,markedSize] at * <;> omega

@[simp] theorem fullMap_mark (b : Blocks c l t) (h : Completion b missing) :
    fullMap b h 59=b.mark := by
  rw [←markedVertex_mark l missing,fullMap_marked]
  exact h.mark_eq


#print axioms low_membership
#print axioms coloring_good
end UniformK60.CommonHost
