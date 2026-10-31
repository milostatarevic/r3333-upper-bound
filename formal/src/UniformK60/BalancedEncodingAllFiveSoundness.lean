import UniformK60.BalancedEncodingAllFiveAux
import UniformK60.BalancedEncodingDegrees
import UniformK60.BalancedHostAllFiveMass

/-! Every actual normalized all-C1 host satisfies its exact all-five input.
The final negative selectors use the proved five-support property. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingAllFive
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.BalancedHost UniformK60.BalancedEncoding UniformK60.HostNormalization
open UniformK61.BalancedEncoding (sat_map sat_flatMap mem_pairs)

set_option maxRecDepth 100000 in
theorem canonical_rootColor : ∀ v : Vertex,v≠0 → canonicalCell true v=some (palette (rootColor v)) := by decide

theorem root_sat {c : Host} {o : Owner} (hn : Normalized true c o)
    (v : Valuation) (hp : PhysicalMatches v c) : FormulaSat v rootClauses := by
  apply sat_map
  intro u hu
  have hu0 : u≠0 := of_decide_eq_true (List.mem_filter.mp hu).2
  have hh := hn.spokes u
  rw [canonical_rootColor u hu0] at hh
  have he := ((mem_colorNeighborhood _ _ _ _).mp
    ((rootCell_some c 0 u (Equiv.refl _) (palette (rootColor u))).mp hh)).2
  refine ⟨positive (edgeVar 0 u (rootColor u)),by simp,?_⟩
  simp [positive,hp _ _ hu0.symm,he]

theorem templates_sat {c : Host} {o : Owner} (hn : Normalized true c o)
    (v : Valuation) (hp : PhysicalMatches v c) : FormulaSat v (templateClauses o) := by
  rw [templateClauses,formulaSat_append]
  constructor
  · apply sat_map
    rintro ⟨a,b⟩ hab
    have hne := ne_of_lt (mem_pairs.mp hab)
    refine ⟨positive (edgeVar (x a) (x b) (foreign 0 (R4333.k16Template o.1 a b))),by simp,?_⟩
    have he := hn.left_template a b hne
    change c (x a) (x b)=_ at he
    have he' : c (x a) (x b)=palette (foreign 0 (R4333.k16Template o.1 a b)) := by simpa only [Fin.castLE] using he
    change v (edgeVar (x a) (x b) (foreign 0 (R4333.k16Template o.1 a b)))=true
    rw [hp (x a) (x b) ((x_injective true).ne hne),he']
    simp
  · apply sat_map
    rintro ⟨a,b⟩ hab
    have hne := ne_of_lt (mem_pairs.mp hab)
    refine ⟨positive (edgeVar (y a) (y b) (foreign 1 (R4333.k16Template o.2 a b))),by simp,?_⟩
    have he := hn.right_template a b hne
    change c (y a) (y b)=_ at he
    have he' : c (y a) (y b)=palette (foreign 1 (R4333.k16Template o.2 a b)) := by simpa only [Fin.castLE] using he
    change v (edgeVar (y a) (y b) (foreign 1 (R4333.k16Template o.2 a b)))=true
    rw [hp (y a) (y b) ((y_injective true).ne hne),he']
    simp

theorem base_bound (clause : List Literal) (hc : clause∈Core.baseCNF)
    (lit : Literal) (hl : lit∈clause) : lit.2<7081 := by
  rcases List.mem_append.mp hc with h | h
  · exact physicalClauses_bound clause h lit hl
  · exact triangleClauses_bound clause h lit hl

theorem normalized_satisfiable {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized true c o) (hall : AllOwnSixteen c) :
    ∃ v : Valuation,FormulaSat v (formula o) := by
  classical
  let old := physicalValuation c
  let ws (s : Scope) := Classical.choose (actual_guard_witness hc hn hall s)
  have five (s : Scope) := Classical.choose_spec (actual_guard_witness hc hn hall s)
  let guardLocals (s : Scope) := extendGuard old (ws s)
  have guardsAgree (s : Scope) (a : Nat) (ha : a≤7080) : guardLocals s a=old a := by
    apply extendGuard_below old (ws s) 7080 _ a ha
    intro i
    have h := (guard_ranges o s).1
    change 7080<guardStart o s+i.val+1
    omega
  let first := mergeBlocks (guardBlock o) old guardLocals 7080
  have firstPhysical : PhysicalMatches first c := by
    intro a b hab q
    have h := (edgeVar_bounds a b q hab).2
    exact (mergeBlocks_physical (guardBlock o) old guardLocals 7080 _ (by omega)).trans
      (BalancedEncodingData.physical_matches c a b hab q)
  have firstSelector (s : Scope) (i : Fin (guardCount o s)) :
      first ((guardGeometry o s).selector i)=decide (i=(ws s).chosen) := by
    have hi : (guardBlock o s).owns ((guardGeometry o s).selector i) := by
      change guardStart o s<guardStart o s+i.val+1 ∧ guardStart o s+i.val+1≤guardStart o s+guardCount o s
      have := i.isLt
      constructor <;> omega
    have hm := mergeBlocks_local (guardBlock o) old guardLocals 7080 (guardBlocks_separate o)
      guardsAgree s ((guardGeometry o s).selector i) (Or.inr hi)
    change first ((guardGeometry o s).selector i)=_ at hm
    rw [hm]
    apply extendGuard_at old (ws s) _ i
    intro a b he
    change guardStart o s+a.val+1=guardStart o s+b.val+1 at he
    exact Fin.ext (by omega)
  have existsLocal (s : Scope) : Nonempty (LocalWitness c (embeddingGeometry o s)) :=
    normalized_local_witness hc hn (scope s) (ready o s)
      (embeddingGeometry o s).roleAtom (embeddingGeometry o s).stateAtom
  let localWitness (s : Scope) := Classical.choice (existsLocal s)
  let embedLocals (s : Scope) := extendLocal first (localWitness s)
  have embeddingsAgree (s : Scope) (a : Nat) (ha : a≤guardTop o) : embedLocals s a=first a :=
    extendLocal_below first (localWitness s) (guardTop o) (embedding_slot_fresh o s) a ha
  let v := mergeBlocks (embeddingBlock o) first embedLocals (guardTop o)
  have preserve (a : Nat) (ha : a≤guardTop o) : v a=first a :=
    mergeBlocks_physical (embeddingBlock o) first embedLocals (guardTop o) a ha
  have hp : PhysicalMatches v c := by
    intro a b hab q
    have hb := (edgeVar_bounds a b q hab).2
    have ht := guardTop_lower o
    exact (preserve _ (by omega)).trans (firstPhysical a b hab q)
  have atSlot (s : Scope) (a : LocalSlot (otherSize (scope s))) :
      v (slotAtom (embeddingGeometry o s) a)=slotValue (localWitness s) a := by
    have hm := mergeBlocks_local (embeddingBlock o) first embedLocals (guardTop o)
      (embeddingBlocks_separate o) embeddingsAgree s (slotAtom (embeddingGeometry o s) a)
      (Or.inr (embedding_slot_owns o s a))
    change v (slotAtom (embeddingGeometry o s) a)=_ at hm
    exact hm.trans (extendLocal_at first (localWitness s) (embedding_slot_injective o s) a)
  have atSelector (s : Scope) (i : Fin (guardCount o s)) :
      v ((guardGeometry o s).selector i)=decide (i=(ws s).chosen) := by
    have hi := i.isLt
    have hb := (guard_ranges o s).2
    exact (preserve _ (by change guardStart o s+i.val+1≤guardTop o;omega)).trans (firstSelector s i)
  have baseSat : FormulaSat v Core.baseCNF := by
    apply formulaSat_congr_below old v Core.baseCNF 7081 base_bound _ (Core.coloring_satisfies_base c hc)
    intro a ha
    have ht := guardTop_lower o
    exact (preserve a (by omega)).trans
      (mergeBlocks_physical (guardBlock o) old guardLocals 7080 a (by omega))
  have guardSat : FormulaSat v (guards o) := by
    apply sat_flatMap
    intro s _
    exact guard_sat v hp (ws s) (atSelector s)
  have embedSat : FormulaSat v (embeddings o) := by
    apply sat_flatMap
    intro s _
    apply embedding_sat v (localWitness s) hp
    · intro m t
      exact atSlot s (.inl (m,t))
    · intro k
      exact atSlot s (.inr k)
  have forbiddenSat := forbidFour_sat v ws five atSelector
  refine ⟨v,?_⟩
  simp only [formula,formulaSat_append]
  exact ⟨⟨⟨⟨⟨baseSat,root_sat hn v hp⟩,templates_sat hn v hp⟩,guardSat⟩,embedSat⟩,forbiddenSat⟩

#print axioms normalized_satisfiable
end UniformK60.BalancedEncodingAllFive
