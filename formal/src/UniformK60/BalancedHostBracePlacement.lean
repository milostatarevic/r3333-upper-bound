import UniformK60.BalancedHostBraceRow
import UniformK60.BalancedHostBraceFacts
import UniformK60.CommonPlacement
import UniformK60.BalancedRawRoot
import UniformK60.BalancedEncodingBraceMaps

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.BalancedHostBracePlacement
open Ramsey61 Finset UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CommonPlacement UniformK60.ClassificationAdapter
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedGeometry UniformK60.BalancedProjectedHost
open UniformK60.BalancedHostBraceGeometry UniformK60.BalancedHostBraceFrame
open UniformK60.BalancedHostBraceRow UniformK60.BalancedHostBraceFacts
open UniformK60.BalancedEncodingBraces

def cell (v : Vertex) : Option FourColor := if v=0 then none else some (palette (rawRootColor v))
def canonicalHost : Host where
  color u v := if u=0 then palette (rawRootColor v) else if v=0 then palette (rawRootColor u) else palette 0
  color_symm u v := by by_cases hu:u=0 <;> by_cases hv:v=0 <;> simp [hu,hv]

theorem cell_none (v : Vertex) : cell v=none ↔ v=0 := by simp [cell]
theorem cell_some (v : Vertex) (q : FourColor) :
    cell v=some q ↔ v∈colorNeighborhood canonicalHost q 0 := by
  simp [cell,canonicalHost,mem_colorNeighborhood]

theorem cell_card : ∀ q : Color,Fintype.card {v : Vertex // cell v=some (palette q)}=
    BalancedRawRoot.rawDegree q := by decide

abbrev Sizes (n : Nat) : Color→Nat := ![n,5,16,15]
def maps {n : Nat} (f : Fin n↪Vertex) (l : Fin 5↪Vertex) (r : Fin 16↪Vertex)
    (m : Fin 15↪Vertex) : ∀ q : Color,Fin (Sizes n q)↪Vertex :=
  Fin.cases f (Fin.cases l (Fin.cases r (Fin.cases m (fun i => Fin.elim0 i))))

def freeVertex {n : Nat} (hn : n≤5) : Fin n↪Vertex :=
  ⟨fun i => vertex (1+i.val),by
    intro a b h;apply Fin.ext
    have hv:=congrArg Fin.val h
    change (1+a.val)%60=(1+b.val)%60 at hv
    rw [Nat.mod_eq_of_lt (by have:=a.isLt;omega),Nat.mod_eq_of_lt (by have:=b.isLt;omega)] at hv
    omega⟩
def fakeVertex : Fin 5↪Vertex :=
  ⟨fun i => vertex (15+i.val),by decide⟩
def realVertex : Fin 16↪Vertex :=
  ⟨fun i => vertex (29+i.val),by decide⟩
def markedVertex : Fin 15↪Vertex :=
  ⟨fun i => vertex (45+i.val),by decide⟩

theorem free_mem {n : Nat} (hn : n≤5) (i : Fin n) :
    freeVertex hn i∈colorNeighborhood canonicalHost (palette 0) 0 := by
  have hi:=i.isLt
  have hb : 1+i.val<60 := by omega
  simp [freeVertex,vertex,mem_colorNeighborhood,canonicalHost,rawRootColor,
    Nat.mod_eq_of_lt hb,show 1+i.val≤14 by omega]
theorem fake_mem : ∀ i,fakeVertex i∈colorNeighborhood canonicalHost (palette 1) 0 := by decide
theorem real_mem : ∀ i,realVertex i∈colorNeighborhood canonicalHost (palette 2) 0 := by decide
theorem marked_mem : ∀ i,markedVertex i∈colorNeighborhood canonicalHost (palette 3) 0 := by decide

/-- Extend the entire visible prescription in one operation. Both low
complements remain free; all31 real and marked critical vertices stay real. -/
theorem place {c : Host} {n : Nat} (hn : n≤5) (root : Vertex)
    (free : Fin n↪Vertex) (fake : Fin 5↪Vertex) (real : Fin 16↪Vertex) (marked : Fin 15↪Vertex)
    (hd : ∀ q : Color,colorDegree c (palette q) root=BalancedRawRoot.rawDegree q)
    (hf : ∀ i,free i∈colorNeighborhood c (palette 0) root)
    (hl : ∀ i,fake i∈colorNeighborhood c (palette 1) root)
    (hr : ∀ i,real i∈colorNeighborhood c (palette 2) root)
    (hm : ∀ i,marked i∈colorNeighborhood c (palette 3) root) :
    ∃ e : Vertex≃Vertex,e 0=root ∧ (∀ v,rootCell c root (Equiv.refl _) (e v)=cell v) ∧
      (∀ i,e (freeVertex hn i)=free i) ∧ (∀ i,e (fakeVertex i)=fake i) ∧
      (∀ i,e (realVertex i)=real i) ∧ (∀ i,e (markedVertex i)=marked i) := by
  let sm := maps (freeVertex hn) fakeVertex realVertex markedVertex
  let tm := maps free fake real marked
  have hs : ∀ q i,sm q i∈colorNeighborhood canonicalHost (palette q) 0 := by
    intro q;fin_cases q
    · exact free_mem hn
    · exact fake_mem
    · exact real_mem
    · exact marked_mem
  have ht : ∀ q i,tm q i∈colorNeighborhood c (palette q) root := by
    intro q;fin_cases q
    · exact hf
    · exact hl
    · exact hr
    · exact hm
  let s := partsEmbedding sm hs
  let t := partsEmbedding tm ht
  have hcard : ∀ q : FourColor,Fintype.card {v : Vertex // cell v=some q}=colorDegree c q root := by
    intro q;obtain ⟨a,rfl⟩:=palette_surjective q
    exact (cell_card a).trans (hd a).symm
  have hlabel : ∀ a,rootCell c root (Equiv.refl _) (t a)=cell (s a) := by
    intro a
    cases a with
    | inl a => change rootCell c root (Equiv.refl _) root=cell 0;simp [rootCell,cell]
    | inr a =>
      rcases a with ⟨q,i⟩
      exact ((rootCell_some c root (tm q i) (Equiv.refl _) (palette q)).mpr (ht q i)).trans
        ((cell_some (sm q i) (palette q)).mpr (hs q i)).symm
  obtain ⟨e,he0,he,hmap⟩ := exists_root_placement c root cell cell_none hcard s t hlabel
  exact ⟨e,he0,he,(fun i => hmap (.inr ⟨0,i⟩)),(fun i => hmap (.inr ⟨1,i⟩)),
    (fun i => hmap (.inr ⟨2,i⟩)),(fun i => hmap (.inr ⟨3,i⟩))⟩

#print axioms place
end UniformK60.BalancedHostBracePlacement
