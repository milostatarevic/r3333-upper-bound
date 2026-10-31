import UniformK60.CEntranceSourceDefs
import UniformK60.CommonPlacement
import UniformK60.CommonEntrance

set_option autoImplicit false
set_option maxRecDepth 100000
namespace UniformK60.CEntranceLayout
open Ramsey61 Finset UniformK60.Physical UniformK60.HostNormalization
open UniformK60.CEntranceSource

/-- Only the root spokes are used to define the canonical cell partition. -/
def canonicalHost (mode : Mode) : Host where
  color u v := if u=0 then palette (rootColor mode v)
    else if v=0 then palette (rootColor mode u) else palette 0
  color_symm u v := by
    by_cases hu : u=0 <;> by_cases hv : v=0 <;> simp [hu,hv]

def cell (mode : Mode) (v : Vertex) : Option FourColor :=
  if v=0 then none else some (palette (rootColor mode v))

def shape (mode : Mode) : Color → Nat :=
  (![![13,16,16,14],![14,16,16,13],![14,15,16,14]] : Fin 3 → Color → Nat) mode

@[simp] theorem cell_none (mode : Mode) (v : Vertex) : cell mode v=none ↔ v=0 := by
  simp [cell]

theorem cell_some (mode : Mode) (v : Vertex) (q : FourColor) :
    cell mode v=some q ↔ v ∈ colorNeighborhood (canonicalHost mode) q 0 := by
  simp [cell,mem_colorNeighborhood,canonicalHost]

theorem cell_card : ∀ mode : Mode,∀ q : Color,
    Fintype.card {v : Vertex // cell mode v=some (palette q)}=shape mode q := by
  decide +kernel

theorem rootColor_mark : ∀ mode : Mode,rootColor mode 59=3 := by decide

theorem canonical_left_mem : ∀ mode : Mode,∀ i : Fin (leftSize mode),
    leftVertex mode i ∈ colorNeighborhood (canonicalHost mode) (palette 1) 0 := by
  decide +kernel

theorem canonical_right_mem : ∀ mode : Mode,∀ i : Fin 16,
    rightVertex mode i ∈ colorNeighborhood (canonicalHost mode) (palette 2) 0 := by
  decide +kernel

theorem canonical_mark_mem : ∀ mode : Mode,
    (59 : Vertex) ∈ colorNeighborhood (canonicalHost mode) (palette 3) 0 := by decide

theorem leftVertex_injective : ∀ mode : Mode,Function.Injective (leftVertex mode) := by
  decide +kernel

theorem rightVertex_injective : ∀ mode : Mode,Function.Injective (rightVertex mode) := by
  decide +kernel

def leftEmbedding (mode : Mode) : Fin (leftSize mode) ↪ Vertex :=
  ⟨leftVertex mode,leftVertex_injective mode⟩

def rightEmbedding (mode : Mode) : Fin 16 ↪ Vertex :=
  ⟨rightVertex mode,rightVertex_injective mode⟩

def markEmbedding : Fin 1 ↪ Vertex := ⟨fun _ => 59,fun _ _ _ => Subsingleton.elim _ _⟩

def freeEmbedding {n : Nat} (hn : n≤5) : Fin n ↪ Vertex where
  toFun i := ⟨1+i.val,by omega⟩
  inj' := by intro a b h;apply Fin.ext;have hv : 1+a.val=1+b.val := congrArg Fin.val h;omega

theorem canonical_free_mem (mode : Mode) {n : Nat} (hn : n≤5) (i : Fin n) :
    freeEmbedding hn i ∈ colorNeighborhood (canonicalHost mode) (palette 0) 0 := by
  apply (mem_colorNeighborhood _ _ _ _).mpr
  constructor
  · intro h
    have hv : 1+i.val=0 := congrArg Fin.val h
    omega
  · change palette (rootColor mode (freeEmbedding hn i))=palette 0
    have hv : (freeEmbedding hn i).val≤lowSize mode := by
      have hm : 13≤lowSize mode := by fin_cases mode <;> decide
      change 1+i.val≤lowSize mode
      omega
    simp only [rootColor,if_pos hv]

/-- Every canonical vertex in a foreign cell has its displayed local index. -/
theorem left_index {mode : Mode} {v : Vertex}
    (h : leftStart mode≤v.val ∧ v.val<rightStart mode) :
    ∃ i : Fin (leftSize mode),leftVertex mode i=v := by
  have hv : v.val-leftStart mode<leftSize mode := by unfold rightStart at h;omega
  refine ⟨⟨v.val-leftStart mode,hv⟩,?_⟩
  apply Fin.ext
  change (leftStart mode+(v.val-leftStart mode))%60=v.val
  rw [Nat.add_sub_of_le h.1,Nat.mod_eq_of_lt v.isLt]

theorem right_index {mode : Mode} {v : Vertex}
    (h : rightStart mode≤v.val ∧ v.val<rightStart mode+16) :
    ∃ i : Fin 16,rightVertex mode i=v := by
  have hv : v.val-rightStart mode<16 := by omega
  refine ⟨⟨v.val-rightStart mode,hv⟩,?_⟩
  apply Fin.ext
  change (rightStart mode+(v.val-rightStart mode))%60=v.val
  rw [Nat.add_sub_of_le h.1,Nat.mod_eq_of_lt v.isLt]

end UniformK60.CEntranceLayout
