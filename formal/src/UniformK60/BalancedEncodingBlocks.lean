import UniformK60.BalancedEncodingDegrees
import UniformK60.BalancedEncodingAuxChecks

/-! Every local block has a witness obtained from the same normalized
physical coloring. Auxiliary choices never replace a physical host edge. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK60.BalancedHost UniformK60.BalancedEncoding

set_option maxRecDepth 100000 in
theorem guard_minor_eq : ∀ s : Scope, guardMinor (scope s) = otherMinor s := by decide

theorem pattern_transport (a b kind : Bool) (h : a=b) (supportSet : Finset (Fin 16))
    (w : ∃ i : BalancedAnchor.PatternIndex a kind,BalancedAnchor.pattern a kind i=supportSet) :
    ∃ i : BalancedAnchor.PatternIndex b kind,BalancedAnchor.pattern b kind i=supportSet := by
  cases h
  exact w

theorem actual_guard_witness {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized false c o) (s : Scope) :
    Nonempty (GuardWitness c (guardGeometry o s)) := by
  obtain ⟨i,hi⟩ := pattern_transport (guardMinor (scope s)) (otherMinor s) (otherKind o (scope s))
    (guard_minor_eq s) (castSet c (scope s)) (actual_guard_pattern hc hn (scope s))
  refine ⟨⟨i,?_⟩⟩
  intro m
  change c (centerVertex (scope s)) (otherVertex (scope s) m) = palette (ownColor (scope s)) ↔
    m ∈ Finset.univ.filter (fun v =>
      Fin.castLE (other_le (scope s)) v ∈ BalancedAnchor.pattern (otherMinor s) (guardKind o s) i)
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hi,cast_mem]
  simp only [guardSet,Finset.mem_filter,Finset.mem_univ,true_and]

theorem actual_guard_extension {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized false c o) (s : Scope) :
    ∃ v : Valuation, FormulaSat v (guardClauses (guardGeometry o s)) ∧
      (∀ a, a ≤ 7080 → v a = physicalValuation c a) := by
  obtain ⟨w⟩ := actual_guard_witness hc hn s
  have hi : Function.Injective (guardGeometry o s).selector := by
    intro a b h
    change guardStart o s+a.val+1=guardStart o s+b.val+1 at h
    exact Fin.ext (by omega)
  have fresh (i) : 7080 < (guardGeometry o s).selector i := by
    have h := (guard_intervals o s).1
    change 7080 < guardStart o s+i.val+1
    change 122259 ≤ guardStart o s at h
    omega
  obtain ⟨v,hv,ha,_⟩ := guard_extension (physicalValuation c) (physical_matches c) w
    7080 (by omega) hi fresh
  exact ⟨v,hv,ha⟩

theorem actual_degree_extension {c : Host} {o : Owner}
    (hn : Normalized false c o) (v : Vertex) (q : Color) :
    ∃ w : Valuation,
      FormulaSat w (SequentialCounter.counter (degreeInput o v q)
        (unknownNeighbors o v).length (degreeBound o v q) (degreeStart o (v,q))) ∧
      ∀ a, a ≤ 7080 → w a = physicalValuation c a := by
  have hlow : 7080 ≤ degreeStart o (v,q) := (degree_interval_bounds o (degreeIndex v q)).1
  have hb (i : Nat) (hi : i < (unknownNeighbors o v).length) :
      degreeInput o v q i ≤ degreeStart o (v,q) :=
    le_trans (degree_input_bound o v q i hi) hlow
  have hc := degree_input_count hn v q
  have hcount : SequentialCounter.prefixCount
      (fun i => physicalValuation c (degreeInput o v q i)) (unknownNeighbors o v).length ≤
      degreeBound o v q := by rw [hc];exact unknownTrue_bound hn v q
  obtain ⟨w,ha,hw⟩ := SequentialCounter.satisfiable_extension (physicalValuation c)
    (degreeInput o v q) (unknownNeighbors o v).length (degreeBound o v q)
    (degreeStart o (v,q)) hb hcount
  exact ⟨w,hw,fun a h => ha a (le_trans h hlow)⟩

theorem embedding_slot_injective (o : Owner) (s : Scope) (h : AnchorReady o (scope s)) :
    Function.Injective (slotAtom (embeddingGeometry o s h)) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨m,t⟩ := a
      obtain ⟨n,u⟩ := b
      change embeddingStart o s+11*m.val+t.val+1=embeddingStart o s+11*n.val+u.val+1 at hab
      have ht := t.isLt
      have hu := u.isLt
      have hmn : m=n := Fin.ext (by omega)
      have htu : t=u := Fin.ext (by omega)
      simp only [hmn,htu]
    | inr k =>
      obtain ⟨m,t⟩ := a
      change embeddingStart o s+11*m.val+t.val+1=embeddingStart o s+11*otherSize (scope s)+k.val+1 at hab
      have hm := m.isLt
      have ht := t.isLt
      omega
  | inr k =>
    cases b with
    | inl b =>
      obtain ⟨m,t⟩ := b
      change embeddingStart o s+11*otherSize (scope s)+k.val+1=embeddingStart o s+11*m.val+t.val+1 at hab
      have hm := m.isLt
      have ht := t.isLt
      omega
    | inr l =>
      change embeddingStart o s+11*otherSize (scope s)+k.val+1=embeddingStart o s+11*otherSize (scope s)+l.val+1 at hab
      have hkl : k=l := Fin.ext (by omega)
      simp only [hkl]

theorem actual_pentagon_extension {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized false c o) (s : Scope)
    (ready : AnchorReady o (scope s)) :
    ∃ v : Valuation, FormulaSat v (embeddingClauses (embeddingGeometry o s ready)) ∧
      (∀ a, a ≤ 7080 → v a = physicalValuation c a) := by
  have hg := normalized_actual_geometry hn (scope s) ready
    (embeddingGeometry o s ready).roleAtom (embeddingGeometry o s ready).stateAtom
  have hfresh (a : LocalSlot (otherSize (scope s))) :
      7080 < slotAtom (embeddingGeometry o s ready) a := by
    have he := (embedding_intervals o s).1
    have hg : 122259 ≤ guardTop o := by
      have hguard := guard_intervals o 0
      change 122259 ≤ guardStart o 0 ∧ _ at hguard
      omega
    cases a with
    | inl a =>
      change 7080 < embeddingStart o s+11*a.1.val+a.2.val+1
      omega
    | inr k =>
      change 7080 < embeddingStart o s+11*otherSize (scope s)+k.val+1
      omega
  obtain ⟨v,hv,ha,_⟩ := actual_embedding_extension hc hg (physicalValuation c)
    (physical_matches c) 7080 (by omega) (embedding_slot_injective o s ready) hfresh
  exact ⟨v,hv,ha⟩

#print axioms actual_guard_extension
#print axioms actual_degree_extension
#print axioms actual_pentagon_extension
end UniformK60.BalancedEncodingData
