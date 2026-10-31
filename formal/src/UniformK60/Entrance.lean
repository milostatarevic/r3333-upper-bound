import UniformK60.Selector

/-! The ordinary entrance from the manuscript. The selector's eligible
exterior witness is a special case, but no ticket-total inequality is
needed for the physical entrance cover. -/
set_option autoImplicit false
namespace UniformK60
open Ramsey61

/-- Any ticket entering a noncritical group of a C1 or C2 root. -/
def CEntranceWitness (c : Host) : Prop := ∃ root mark,
  (W c root=32 ∨ W c root=31) ∧ mark∈Incoming c root ∧ mark∉Own c root

theorem entrance_witness_iff (c : Host) : CEntranceWitness c ↔
    ∃ root mark, (W c root=32 ∨ W c root=31) ∧ mark≠root ∧
      colorDegree c (c root mark) root<15 ∧
      15≤colorDegree c (c root mark) mark := by
  simp only [CEntranceWitness, ← witness_edge_semantics]

theorem exterior_is_entrance (c : Host) (h : CExteriorWitness c) :
    CEntranceWitness c := by
  obtain ⟨root,mark,hw,_,hin,hout⟩ := h
  exact ⟨root,mark,hw,hin,hout⟩

#print axioms entrance_witness_iff
#print axioms exterior_is_entrance
end UniformK60
