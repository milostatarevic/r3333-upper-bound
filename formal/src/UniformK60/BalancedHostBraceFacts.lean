import UniformK60.BalancedEncodingBraces
import UniformK61.BalancedEncodingLocal

set_option autoImplicit false
namespace UniformK60.BalancedHostBraceFacts
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.BalancedProjectedData UniformK60.BalancedEncodingBraces
open UniformK61.BalancedEncoding (mem_pairs)

/-- All clauses in a raw brace input are accounted for by actual physical
spokes, two complete critical cells, the brace word, and exact membership. -/
structure RawWitness (c : Host) (r : Row) (m : MarkChoice) : Prop where
  spokes : ∀ v : Vertex,v≠0 → c 0 v=palette (rawRootColor v)
  real : ∀ a b : Fin 16,a≠b →
    c (vertex (29+a.val)) (vertex (29+b.val))=
      palette (foreign 2 (R4333.k16Template (rowKind r) a b))
  marked : ∀ a b : Fin 15,a≠b →
    c (vertex (45+a.val)) (vertex (45+b.val))=
      palette (foreign 3 (R4333.k16Template (markedKind m)
        (markedOrder m a).castSucc (markedOrder m b).castSucc))
  matrix : ∀ a b : Fin 15,a≠b → a.val<(rowShape r).dimension → b.val<(rowShape r).dimension →
    c (rawSupport r a) (rawSupport r b)=palette (rowMatrix r a b)
  membership : ∀ v : Vertex,1≤v.val → v.val<59 → (c 59 v=palette 3 ↔ rawBrace r v=true)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rawSupport_ne : ∀ r (a b : Fin 15),a.val<(rowShape r).dimension →
    b.val<(rowShape r).dimension → a≠b → rawSupport r a≠rawSupport r b := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cross_valid : ∀ r,∀ code∈(crossOrders[r.val]!).toList,
    coord (code%16)≠coord (code/16) ∧
      (coord (code%16)).val<(rowShape r).dimension ∧
      (coord (code/16)).val<(rowShape r).dimension := by decide +kernel

set_option maxRecDepth 1000000 in
theorem free_facts : ∀ r (a b : Fin 5),a<b → b.val<freeSize r →
    coord a.val≠coord b.val ∧ (coord a.val).val<(rowShape r).dimension ∧
      (coord b.val).val<(rowShape r).dimension ∧
      rawSupport r (coord a.val)=vertex (1+a.val) ∧
      rawSupport r (coord b.val)=vertex (1+b.val) := by decide

set_option maxRecDepth 1000000 in
theorem fake_facts : ∀ r (a b : Fin 5),a<b →
    coord (freeSize r+a.val)≠coord (freeSize r+b.val) ∧
      (coord (freeSize r+a.val)).val<(rowShape r).dimension ∧
      (coord (freeSize r+b.val)).val<(rowShape r).dimension ∧
      rawSupport r (coord (freeSize r+a.val))=vertex (15+a.val) ∧
      rawSupport r (coord (freeSize r+b.val))=vertex (15+b.val) := by decide

private theorem signed_match (c : Host) (u v : Vertex) (hne : u≠v) (q : Color) (b : Bool)
    (h : c u v=palette q ↔ b=true) : Core.UnitMatches c ⟨b,u,v,q⟩ := by
  refine ⟨hne,?_⟩
  cases b
  · exact fun he => Bool.false_ne_true (h.mp he)
  · exact h.mpr rfl

/-- Exact fact-list soundness, preserving both signs and the frozen order. -/
theorem raw_units_match {c : Host} {r : Row} {m : MarkChoice} (w : RawWitness c r m) :
    Core.UnitsMatch c (rawUnits r m) := by
  intro u hu
  simp only [rawUnits,rawRootUnits,rawRealUnits,rawMarkedUnits,List.mem_append] at hu
  rcases hu with (((((hu|hu)|hu)|hu)|hu)|hu)|hu
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    have hn : v≠0 := of_decide_eq_true (List.mem_filter.mp hv).2
    exact ⟨hn.symm,w.spokes v hn⟩
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hu
    have hn : ab.1≠ab.2 := ne_of_lt (mem_pairs.mp hab)
    refine ⟨?_,w.real ab.1 ab.2 hn⟩
    intro h
    apply hn
    apply Fin.ext
    have hh := congrArg Fin.val h
    change (29+ab.1.val)%60=(29+ab.2.val)%60 at hh
    rw [Nat.mod_eq_of_lt (by have:=ab.1.isLt;omega),Nat.mod_eq_of_lt (by have:=ab.2.isLt;omega)] at hh
    omega
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hu
    have hn : ab.1≠ab.2 := ne_of_lt (mem_pairs.mp hab)
    refine ⟨?_,w.marked ab.1 ab.2 hn⟩
    intro h
    apply hn
    apply Fin.ext
    have hh := congrArg Fin.val h
    change (45+ab.1.val)%60=(45+ab.2.val)%60 at hh
    rw [Nat.mod_eq_of_lt (by have:=ab.1.isLt;omega),Nat.mod_eq_of_lt (by have:=ab.2.isLt;omega)] at hh
    omega
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hu
    have hab' := List.mem_filter.mp hab
    have hlt := mem_pairs.mp hab'.1
    have hb := of_decide_eq_true hab'.2
    obtain ⟨hn,ha,hb',hea,heb⟩ := free_facts r ab.1 ab.2 hlt hb
    have he := w.matrix _ _ hn ha hb'
    have hne := rawSupport_ne r _ _ ha hb' hn
    rw [hea,heb] at he hne
    exact ⟨hne,he⟩
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hn,ha,hb,hea,heb⟩ := fake_facts r ab.1 ab.2 (mem_pairs.mp hab)
    have he := w.matrix _ _ hn ha hb
    have hne := rawSupport_ne r _ _ ha hb hn
    rw [hea,heb] at he hne
    exact ⟨hne,he⟩
  · obtain ⟨code,hcode,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hn,ha,hb⟩ := cross_valid r code hcode
    exact ⟨rawSupport_ne r _ _ ha hb hn,w.matrix _ _ hn ha hb⟩
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    have h := of_decide_eq_true (List.mem_filter.mp hv).2
    exact signed_match c 59 v (by intro he;have hh:=congrArg Fin.val he;omega) 3 _
      (w.membership v h.1 h.2)

#print axioms raw_units_match
end UniformK60.BalancedHostBraceFacts
