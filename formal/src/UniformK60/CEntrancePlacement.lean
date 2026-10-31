import UniformK60.CEntranceLayout

/-! Simultaneous physical placement for entrance configurations. Only the
selected low support, the two actual foreign cells, and the mark are fixed. -/
set_option autoImplicit false
namespace UniformK60.CEntrancePlacement
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CommonPlacement UniformK60.CEntranceSource UniformK60.CEntranceLayout

abbrev Sizes (mode : Mode) (n : Nat) : Color → Nat := ![n,leftSize mode,16,1]

def maps {mode : Mode} {n : Nat} (f : Fin n ↪ Vertex)
    (l : Fin (leftSize mode) ↪ Vertex) (r : Fin 16 ↪ Vertex)
    (m : Fin 1 ↪ Vertex) : ∀ q : Color,Fin (Sizes mode n q) ↪ Vertex :=
  Fin.cases f (Fin.cases l (Fin.cases r (Fin.cases m (fun i => Fin.elim0 i))))

noncomputable def singleton (v : Vertex) : Fin 1 ↪ Vertex :=
  ⟨fun _ => v,fun _ _ _ => Subsingleton.elim _ _⟩

/-- This one equivalence places all visible vertices together; every other
vertex is filled inside its prescribed root cell. -/
theorem place {c : Host} {mode : Mode} {n : Nat} (hn : n≤5)
    (root mark : Vertex)
    (free : Fin n ↪ Vertex) (left : Fin (leftSize mode) ↪ Vertex)
    (right : Fin 16 ↪ Vertex)
    (hd : ∀ q : Color,colorDegree c (palette q) root=shape mode q)
    (hf : ∀ i,free i∈colorNeighborhood c (palette 0) root)
    (hl : ∀ i,left i∈colorNeighborhood c (palette 1) root)
    (hr : ∀ i,right i∈colorNeighborhood c (palette 2) root)
    (hm : mark∈colorNeighborhood c (palette 3) root) :
    ∃ e : Vertex ≃ Vertex,e 0=root ∧
      (∀ v,rootCell c root (Equiv.refl _) (e v)=cell mode v) ∧
      (∀ i,e (freeEmbedding hn i)=free i) ∧
      (∀ i,e (leftVertex mode i)=left i) ∧
      (∀ i,e (rightVertex mode i)=right i) ∧ e 59=mark := by
  let sm := maps (freeEmbedding hn) (leftEmbedding mode) (rightEmbedding mode) markEmbedding
  let tm := maps free left right (singleton mark)
  have hs : ∀ q i,sm q i∈colorNeighborhood (canonicalHost mode) (palette q) 0 := by
    intro q
    fin_cases q
    · exact canonical_free_mem mode hn
    · exact canonical_left_mem mode
    · exact canonical_right_mem mode
    · intro i;exact canonical_mark_mem mode
  have ht : ∀ q i,tm q i∈colorNeighborhood c (palette q) root := by
    intro q
    fin_cases q
    · exact hf
    · exact hl
    · exact hr
    · intro i;exact hm
  let s := partsEmbedding sm hs
  let t := partsEmbedding tm ht
  have hcard : ∀ q : FourColor,Fintype.card {v : Vertex // cell mode v=some q}=
      colorDegree c q root := by
    intro q
    obtain ⟨a,rfl⟩ := palette_surjective q
    exact (cell_card mode a).trans (hd a).symm
  have hlabel : ∀ a,rootCell c root (Equiv.refl _) (t a)=cell mode (s a) := by
    intro a
    cases a with
    | inl a =>
      change rootCell c root (Equiv.refl _) root=cell mode 0
      simp [rootCell,cell]
    | inr a =>
      rcases a with ⟨q,i⟩
      change rootCell c root (Equiv.refl _) (tm q i)=cell mode (sm q i)
      have htarget := (rootCell_some c root (tm q i) (Equiv.refl _) (palette q)).mpr (ht q i)
      have hsource := (cell_some mode (sm q i) (palette q)).mpr (hs q i)
      exact htarget.trans hsource.symm
  obtain ⟨e,he0,he,hmap⟩ := exists_root_placement c root (cell mode) (cell_none mode) hcard s t hlabel
  refine ⟨e,he0,he,?_,?_,?_,?_⟩
  · intro i;exact hmap (.inr ⟨0,i⟩)
  · intro i;exact hmap (.inr ⟨1,i⟩)
  · intro i;exact hmap (.inr ⟨2,i⟩)
  · exact hmap (.inr ⟨3,⟨0,by change 0<1;decide⟩⟩)

#print axioms place
end UniformK60.CEntrancePlacement
