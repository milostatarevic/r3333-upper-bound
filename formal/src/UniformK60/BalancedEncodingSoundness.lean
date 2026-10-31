import UniformK60.BalancedEncodingDegreeValuation
import UniformK60.BalancedEncodingEmbeddingValuation

/-! Actual normalized mixed-C1/C2 hosts satisfy the exact compatibility
prefix. All auxiliary witnesses are constructed after one host normalization. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.BalancedHost UniformK60.BalancedEncoding UniformK60.HostNormalization
open UniformK61.BalancedEncoding (sat_map mem_pairs)

theorem root_sat {c : Host} {o : Owner} (hn : Normalized false c o)
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

theorem templates_sat {c : Host} {o : Owner} (hn : Normalized false c o)
    (v : Valuation) (hp : PhysicalMatches v c) : FormulaSat v (templateClauses o) := by
  rw [templateClauses,formulaSat_append]
  constructor
  · apply sat_map
    rintro ⟨a,b⟩ hab
    have hne := ne_of_lt (mem_pairs.mp hab)
    refine ⟨positive (edgeVar (x a) (x b) (foreign 0 (R4333.k16Template o.1 a.castSucc b.castSucc))),by simp,?_⟩
    have he := hn.left_template a b hne
    change c (x a) (x b)=_ at he
    have he' : c (x a) (x b)=palette (foreign 0 (R4333.k16Template o.1 a.castSucc b.castSucc)) := by
      simpa only [Fin.castLE,Fin.castSucc,Fin.castAdd] using he
    change v (edgeVar (x a) (x b) (foreign 0 (R4333.k16Template o.1 a.castSucc b.castSucc)))=true
    rw [hp (x a) (x b) ((x_injective false).ne hne),he']
    simp
  · apply sat_map
    rintro ⟨a,b⟩ hab
    have hne := ne_of_lt (mem_pairs.mp hab)
    refine ⟨positive (edgeVar (y a) (y b) (foreign 1 (R4333.k16Template o.2 a b))),by simp,?_⟩
    have he := hn.right_template a b hne
    change c (y a) (y b)=_ at he
    have he' : c (y a) (y b)=palette (foreign 1 (R4333.k16Template o.2 a b)) := by
      simpa only [Fin.castLE] using he
    change v (edgeVar (y a) (y b) (foreign 1 (R4333.k16Template o.2 a b)))=true
    rw [hp (y a) (y b) ((y_injective false).ne hne),he']
    simp

theorem base_bound (clause : List Literal) (hc : clause∈Core.baseCNF)
    (lit : Literal) (hl : lit∈clause) : lit.2<7081 := by
  rcases List.mem_append.mp hc with h | h
  · exact physicalClauses_bound clause h lit hl
  · exact triangleClauses_bound clause h lit hl

theorem degrees_bound (o : Owner) (clause : List Literal) (hc : clause∈degreeClauses o)
    (lit : Literal) (hl : lit∈clause) : lit.2≤degreeTop o := by
  obtain ⟨⟨v,q⟩,_,hcl⟩ := List.mem_flatMap.mp hc
  have hs := SequentialCounter.counter_atoms_input_or_fresh (degreeInput o v q)
    (unknownNeighbors o v).length (degreeBound o v q) (degreeStart o (v,q)) clause hcl lit hl
  rcases hs with ⟨i,hi,he⟩ | hs
  · rw [he]
    have h := degree_input_bound o v q i hi
    change degreeInput o v q i≤122259
    omega
  · rw [degree_counter_end] at hs
    have he := (degree_interval_bounds o (degreeIndex v q)).2.2
    exact le_trans hs.2 he

theorem normalized_satisfiable {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized false c o) :
    ∃ v : Valuation,FormulaSat v (formula o) ∧
      ∀ a,a≤7080 → v a=physicalValuation c a := by
  obtain ⟨v1,hdegree,hp1⟩ := actual_degree_family_extension hn
  have physical1 : PhysicalMatches v1 c := by
    intro a b hab q
    have hb := (edgeVar_bounds a b q hab).2
    exact (hp1 _ (by omega)).trans (physical_matches c a b hab q)
  obtain ⟨v2,hguard,hp2⟩ := actual_guard_family_extension hc hn v1 physical1
  have physical2 : PhysicalMatches v2 c := by
    intro a b hab q
    have hb := (edgeVar_bounds a b q hab).2
    exact (hp2 _ (by change edgeVar a b q≤122259;omega)).trans (physical1 a b hab q)
  obtain ⟨v3,hembed,hp3⟩ := actual_embedding_family_extension hc hn v2 physical2
  have hg := guardTop_lower o
  have physical3 : PhysicalMatches v3 c := by
    intro a b hab q
    have hb := (edgeVar_bounds a b q hab).2
    have htop : 122259≤guardTop o := hg
    exact (hp3 _ (by omega)).trans (physical2 a b hab q)
  have unchanged (a : Nat) (ha : a≤7080) : v3 a=physicalValuation c a := by
    have htop : 122259≤guardTop o := hg
    exact (hp3 a (by omega)).trans ((hp2 a (by change a≤122259;omega)).trans (hp1 a ha))
  refine ⟨v3,?_,unchanged⟩
  simp only [formula,extra,formulaSat_append]
  refine ⟨?_,⟨⟨⟨root_sat hn v3 physical3,templates_sat hn v3 physical3⟩,?_⟩,?_⟩,hembed⟩
  · exact formulaSat_congr_below (physicalValuation c) v3 Core.baseCNF 7081 base_bound
      (fun a h=>unchanged a (by omega)) (Core.coloring_satisfies_base c hc)
  · apply formulaSat_congr_below v1 v3 (degreeClauses o) (degreeTop o+1)
    · intro clause hcl lit hl
      have h := degrees_bound o clause hcl lit hl;omega
    · intro a ha
      have h : a≤degreeTop o := by omega
      exact (hp3 a (le_trans h hg)).trans (hp2 a h)
    · exact hdegree
  · apply formulaSat_congr_below v2 v3 (guards o) (guardTop o+1)
    · intro clause hcl lit hl
      have h := guards_bound o clause hcl lit hl;omega
    · intro a ha
      exact hp3 a (by omega)
    · exact hguard

/-- Exact additional brace facts use the physical valuation already shared
by every compatibility block. -/
theorem normalized_units_satisfiable {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized false c o)
    (us : List Core.PhysicalUnit) (hu : Core.UnitsMatch c us) :
    ∃ v : Valuation,FormulaSat v (formula o ++ Core.unitsCNF us) := by
  obtain ⟨v,hv,hp⟩ := normalized_satisfiable hc hn
  refine ⟨v,(formulaSat_append _ _ _).mpr ⟨hv,?_⟩⟩
  apply formulaSat_congr_below (physicalValuation c) v (Core.unitsCNF us) 7081
  · intro clause hcl lit hl
    obtain ⟨u,hum,rfl⟩ := List.mem_map.mp hcl
    have he := List.mem_singleton.mp hl
    subst lit
    exact (Core.unitLiteral_bounds u (hu u hum).1).2
  · intro a ha
    exact hp a (by omega)
  · exact Core.units_match_satisfies c us hu

#print axioms normalized_satisfiable
#print axioms normalized_units_satisfiable
end UniformK60.BalancedEncodingData
