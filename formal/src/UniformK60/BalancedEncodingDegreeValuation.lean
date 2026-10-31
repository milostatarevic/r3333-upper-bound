import UniformK60.BalancedEncodingBlocks
import UniformK60.BalancedEncodingMerge
import UniformK60.SequentialCounterSupport

/-! Assembly of the240 generic degree counters, sharing one physical host. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK60.BalancedHost UniformK60.BalancedEncoding

def indexVertex (i : DegreeIndex) : Vertex := ⟨i.val/4,by have := i.isLt;omega⟩
def indexColor (i : DegreeIndex) : Color := ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
def indexSlot (i : DegreeIndex) : DegreeSlot := (indexVertex i,indexColor i)

theorem indexSlot_index (v : Vertex) (q : Color) : indexSlot (degreeIndex v q)=(v,q) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp only [indexSlot,indexVertex,indexColor,degreeIndex,Fin.val_mk]
  · have := q.isLt;omega
  · have := q.isLt;omega

theorem degreeIndex_slot (i : DegreeIndex) : degreeIndex (indexVertex i) (indexColor i)=i := by
  apply Fin.ext
  simp only [degreeIndex,indexVertex,indexColor,Fin.val_mk]
  omega

theorem degreeStart_slot (o : Owner) (i : DegreeIndex) : degreeStart o (indexSlot i)=degreeStartAt o i := by
  unfold degreeStart BalancedAuxData.degreeStart degreeStartAt indexSlot
  have he := congrArg Fin.val (degreeIndex_slot i)
  change 4*(indexVertex i).val+(indexColor i).val=i.val at he
  rw [he]

theorem degreeEnd_slot (o : Owner) (i : DegreeIndex) : degreeEnd o (indexSlot i)=degreeEndAt o i := by
  unfold degreeEnd BalancedAuxData.degreeEnd degreeEndAt indexSlot
  have he := congrArg Fin.val (degreeIndex_slot i)
  change 4*(indexVertex i).val+(indexColor i).val=i.val at he
  rw [he]

def degreeBlock (o : Owner) (i : DegreeIndex) : Block where
  lower := degreeStart o (indexSlot i)
  upper := degreeEnd o (indexSlot i)
  clauses := SequentialCounter.counter (degreeInput o (indexVertex i) (indexColor i))
    (unknownNeighbors o (indexVertex i)).length (degreeBound o (indexVertex i) (indexColor i))
    (degreeStart o (indexSlot i))

theorem degreeBlocks_separate (o : Owner) (i j : DegreeIndex) (a : Nat)
    (hi : (degreeBlock o i).owns a) (hj : (degreeBlock o j).owns a) : i=j := by
  apply degree_intervals_separate o i j a
  · simpa only [Block.owns,degreeBlock,degreeStart_slot,degreeEnd_slot] using hi
  · simpa only [Block.owns,degreeBlock,degreeStart_slot,degreeEnd_slot] using hj

theorem degreeBlock_support (o : Owner) (i : DegreeIndex) (clause : List Literal)
    (hc : clause∈(degreeBlock o i).clauses) (lit : Literal) (hl : lit∈clause) :
    lit.2≤7080 ∨ (degreeBlock o i).owns lit.2 := by
  have h := SequentialCounter.counter_atoms_input_or_fresh
    (degreeInput o (indexVertex i) (indexColor i)) (unknownNeighbors o (indexVertex i)).length
    (degreeBound o (indexVertex i) (indexColor i)) (degreeStart o (indexSlot i)) clause hc lit hl
  rcases h with ⟨j,hj,he⟩ | h
  · left
    rw [he]
    exact degree_input_bound o (indexVertex i) (indexColor i) j hj
  · right
    change degreeStart o (indexSlot i)<lit.2 ∧ lit.2≤degreeEnd o (indexSlot i)
    change _ ∧ lit.2≤SequentialCounter.finalTop _ _ (degreeStart o (indexVertex i,indexColor i)) at h
    rw [degree_counter_end] at h
    exact h

theorem actual_degree_family_extension {c : Host} {o : Owner}
    (hn : Normalized false c o) :
    ∃ w : Valuation, FormulaSat w (degreeClauses o) ∧
      ∀ a,a≤7080 → w a=physicalValuation c a := by
  have local_sat (i : DegreeIndex) : ∃ w : Valuation,FormulaSat w (degreeBlock o i).clauses ∧
      ∀ a,a≤7080 → w a=physicalValuation c a :=
    actual_degree_extension hn (indexVertex i) (indexColor i)
  obtain ⟨w,hw,ha⟩ := blocks_satisfiable (degreeBlock o) (physicalValuation c) 7080
    (degreeBlocks_separate o) (degreeBlock_support o) local_sat
  refine ⟨w,?_,ha⟩
  intro clause hc
  obtain ⟨d,hd,hcl⟩ := List.mem_flatMap.mp hc
  obtain ⟨v,_,hq⟩ := List.mem_flatMap.mp hd
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hq
  apply hw clause
  apply List.mem_flatMap.mpr
  refine ⟨degreeIndex v q,List.mem_finRange _,?_⟩
  have hi := indexSlot_index v q
  have hv := congrArg Prod.fst hi
  have hq := congrArg Prod.snd hi
  change indexVertex (degreeIndex v q)=v at hv
  change indexColor (degreeIndex v q)=q at hq
  simpa only [degreeBlock,indexSlot,hv,hq] using hcl

#print axioms actual_degree_family_extension
end UniformK60.BalancedEncodingData
