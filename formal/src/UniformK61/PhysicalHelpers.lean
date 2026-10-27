import UniformK61.Physical
import R4333Lean.FiniteColorCNF

namespace UniformK61.PhysicalHelpers
open Ramsey61 Ramsey61.CEncodingCore
open R4333.FiniteColorCNF

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


theorem mem_edges_bounds {n a b : Nat} (h : (a,b) ∈ edges n) : a < n ∧ b < n ∧ a < b := by
  simp only [edges,vertices,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq] at h
  obtain ⟨x,hx,y,⟨hy,hxy⟩,he⟩ := h
  cases he
  exact ⟨hx,hy,hxy⟩


end UniformK61.PhysicalHelpers
